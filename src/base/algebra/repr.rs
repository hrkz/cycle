use std::cmp::Ordering;
use std::fmt;
use std::iter;
use std::mem;
use std::ops::{Add, BitOr, Div, Mul, Neg, Rem, Shl, Shr, Sub};

pub(crate) type Word = u64;
pub(crate) type Dual = u128;
pub(crate) type Array = Vec<Word>;

pub(crate) const WORD_BYTES: usize = mem::size_of::<Word>();
pub(crate) const WORD_BITS: usize = 8 * WORD_BYTES;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub(crate) enum Digits {
  /// A fixed number of digits represented by a Word.
  Fix(Word),
  /// An arbitrary number of digits.
  Arb(Array),
}

impl Digits {
  fn len(&self) -> usize {
    if let Digits::Arb(array) = &self {
      array.len()
    } else {
      1
    }
  }

  pub(crate) fn is_power_of_two(&self) -> bool {
    match self {
      Digits::Fix(word) => {
        word.is_power_of_two() //.
      }
      Digits::Arb(array) => {
        array[..array.len() - 1].iter().all(|x| *x == 0)
          && array
            .last()
            .unwrap() // > 1
            .is_power_of_two()
      }
    }
  }

  #[inline]
  pub(crate) fn leading_zeros(&self) -> usize {
    match self {
      Digits::Fix(word) => {
        word.leading_zeros() as usize //.
      }
      Digits::Arb(array) => array
        .iter()
        .enumerate()
        .rev()
        .find(|(_, word)| *word != &0)
        .map_or(0, |(idx, word)| idx * WORD_BITS as usize + word.leading_zeros() as usize),
    }
  }

  #[inline]
  pub(crate) fn trailing_zeros(&self) -> usize {
    match self {
      Digits::Fix(word) => {
        word.trailing_zeros() as usize //.
      }
      Digits::Arb(array) => array
        .iter()
        .enumerate()
        .find(|(_, word)| *word != &0)
        .map_or(0, |(idx, word)| idx * WORD_BITS as usize + word.trailing_zeros() as usize),
    }
  }

  pub(crate) fn from_le_bytes(bytes: &[u8]) -> Digits {
    if bytes.len() < WORD_BYTES {
      Digits::Fix(Word::from_le_bytes(
        bytes.try_into().unwrap(), // len < WORD_BYTES
      ))
    } else {
      let mut digits = Array::with_capacity((bytes.len() - 1) / WORD_BYTES + 1);
      let mut chunks = bytes.chunks_exact(WORD_BYTES);
      for chunk in &mut chunks {
        digits.push(Word::from_le_bytes(
          chunk.try_into().unwrap(), // len < WORD_BYTES
        ));
      }
      if !chunks.remainder().is_empty() {
        digits.push(Word::from_le_bytes(
          chunks.remainder().try_into().unwrap(), // len < WORD_BYTES
        ));
      }
      Digits::from(digits)
    }
  }

  pub(crate) fn parse(src: &str, radix: u32) -> Result<Digits, ParseError> {
    let basis = Basis::new(radix);
    let bytes = src.as_bytes();

    if bytes.len() <= basis.digits_per_word {
      Ok(Digits::Fix(parse_word(bytes, radix)?))
    } else {
      let chunks = bytes.rchunks(basis.digits_per_word);
      let mut digits = Array::with_capacity(chunks.len());
      for chunk in chunks.rev() {
        let carry = carrying_mul_word(&mut digits, basis.range_per_word, parse_word(chunk, radix)?);
        if carry != 0 {
          digits.push(carry);
        }
      }
      Ok(Digits::from(digits))
    }
  }
}

fn cmp_digits(lhs: &[Word], rhs: &[Word]) -> Ordering {
  assert!(lhs.len() == rhs.len());
  lhs.iter().rev().cmp(rhs.iter().rev())
}

impl PartialOrd for Digits {
  #[inline]
  fn partial_cmp(&self, o: &Digits) -> Option<Ordering> {
    Some(self.cmp(o))
  }
}

impl Ord for Digits {
  #[inline]
  fn cmp(&self, o: &Digits) -> Ordering {
    match (&self, &o) {
      (Digits::Fix(lhs), Digits::Fix(rhs)) => lhs.cmp(rhs),
      (Digits::Fix(_), Digits::Arb(_)) => Ordering::Less,
      (Digits::Arb(_), Digits::Fix(_)) => Ordering::Greater,
      (Digits::Arb(lhs), Digits::Arb(rhs)) => lhs.len().cmp(&rhs.len()).then_with(
        || cmp_digits(lhs, rhs), //.
      ),
    }
  }
}

impl From<Array> for Digits {
  fn from(mut array: Array) -> Digits {
    while let Some(0) = array.last() {
      array.pop();
    }

    match array.len() {
      0 => Digits::Fix(0),
      1 => Digits::Fix(array[0]),
      _ => {
        array.shrink_to_fit();
        Digits::Arb(
          array, //.
        )
      }
    }
  }
}

impl From<Word> for Digits {
  fn from(word: Word) -> Digits {
    Digits::Fix(word)
  }
}

const fn extend_word(word: Word) -> Dual {
  word as Dual
}

const fn dual_word(lo: Word, hi: Word) -> Dual {
  extend_word(lo) | extend_word(hi) << WORD_BITS
}

const fn split_dual(dual: Dual) -> (Word, Word) {
  (dual as Word, (dual >> WORD_BITS) as Word)
}

fn push_carry(lhs: &mut Array, carry: Word) {
  if carry != 0 {
    lhs.push(carry)
  }
}

#[inline]
fn add_with_carry(lhs: Word, rhs: Word, carry: bool) -> (Word, bool) {
  let (sum, c0) = lhs.overflowing_add(rhs);
  let (sum, c1) = sum.overflowing_add(Word::from(carry));
  (sum, c0 | c1)
}

#[inline]
fn sub_with_borrow(lhs: Word, rhs: Word, borrow: bool) -> (Word, bool) {
  let (sub, c0) = lhs.overflowing_sub(rhs);
  let (sub, c1) = sub.overflowing_sub(Word::from(borrow));
  (sub, c0 | c1)
}

#[inline]
fn carrying_add(lhs: &mut [Word], rhs: &[Word]) -> bool {
  let mut carry = false;
  lhs.iter_mut().zip(rhs.iter()).for_each(|(l, r)| {
    (*l, carry) = add_with_carry(*l, *r, carry);
  });
  carry
}

#[inline]
fn borrowing_sub_lhs(lhs: &mut [Word], rhs: &[Word]) -> bool {
  let mut borrow = false;
  lhs.iter_mut().zip(rhs.iter()).for_each(|(l, r)| {
    (*l, borrow) = sub_with_borrow(*l, *r, borrow);
  });
  borrow
}

#[inline]
fn borrowing_sub_rhs(lhs: &[Word], rhs: &mut [Word]) -> bool {
  debug_assert!(lhs.len() == rhs.len());
  let mut borrow = false;
  lhs.iter().zip(rhs.iter_mut()).for_each(|(l, r)| {
    (*r, borrow) = sub_with_borrow(*l, *r, borrow);
  });
  borrow
}

#[inline]
fn carrying_mul_add(lhs: &mut [Word], mul: &[Word], add: &[Word]) -> bool {
  let mut carry = false;
  add.iter().enumerate().for_each(|(i, a)| {
    let carry_word = lhs[i..].iter_mut().zip(mul.iter()).fold(0, |carry, (l, m)| {
      let (v_lo, v_hi) = split_dual(extend_word(*l) + extend_word(carry) + extend_word(*a) * extend_word(*m));
      *l = v_lo;
      v_hi
    });

    let carry_i = i + mul.len();
    (lhs[carry_i], carry) = add_with_carry(lhs[carry_i], carry_word, carry);
  });
  carry
}

#[inline]
fn borrowing_mul_sub(lhs: &mut [Word], mul: Word, sub: &[Word]) -> Word {
  let mut rcarry = Word::MAX;
  lhs.iter_mut().zip(sub.iter()).for_each(|(l, r)| {
    let v = extend_word(*l) + extend_word(rcarry) + (dual_word(0, Word::MAX) - extend_word(Word::MAX)) - extend_word(mul) * extend_word(*r);
    let (v_lo, v_hi) = split_dual(v);
    *l = v_lo;
    rcarry = v_hi;
  });
  Word::MAX - rcarry
}

#[inline]
fn overflowing_add_word(lhs: &mut [Word], rhs: Word) -> bool {
  for word in lhs {
    let (a, overflow) = word.overflowing_add(rhs);
    *word = a;
    if !overflow {
      return false;
    }
  }
  true
}

#[inline]
fn borrowing_sub_word(lhs: &mut [Word], rhs: Word) -> bool {
  for word in lhs {
    let (a, borrow) = word.overflowing_sub(rhs);
    *word = a;
    if !borrow {
      return false;
    }
  }
  true
}

#[inline]
fn carrying_mul_word(lhs: &mut [Word], rhs: Word, mut carry: Word) -> Word {
  lhs.iter_mut().for_each(|word| {
    (*word, carry) = split_dual(extend_word(*word) * extend_word(rhs) + extend_word(carry));
  });
  carry
}

#[inline]
fn carrying_shl_word(lhs: &mut [Word], shift: u32) -> Word {
  if shift == 0 {
    return 0;
  }
  lhs.iter_mut().fold(0, |carry, word| {
    let (w, c) = split_dual(extend_word(*word) << shift);
    *word = w | carry;
    c
  })
}

#[inline]
fn carrying_shr_word(lhs: &mut [Word], shift: u32) -> Word {
  if shift == 0 {
    return 0;
  }
  lhs.iter_mut().rev().fold(0, |carry, word| {
    let (c, w) = split_dual(dual_word(0, *word) >> shift);
    *word = w | carry;
    c
  }) >> (WORD_BITS as u32 - shift)
}

#[inline]
fn remainding_div_word(lhs: &mut [Word], rhs: Word) -> Word {
  if rhs.is_power_of_two() {
    carrying_shr_word(lhs, rhs.trailing_zeros())
  } else {
    Normalizer::new(rhs << rhs.leading_zeros()).remainding_div_word(
      lhs, //.
      rhs,
    )
  }
}

impl Add<Digits> for Digits {
  type Output = Digits;

  fn add(self, o: Digits) -> Self::Output {
    match (self, o) {
      (Digits::Fix(lhs), Digits::Fix(rhs)) => {
        let (add, overflow) = lhs.overflowing_add(rhs);
        if overflow {
          Digits::Arb(vec![
            add, // carry
            1,
          ])
        } else {
          Digits::Fix(add)
        }
      }

      (Digits::Arb(mut s), o) | (o, Digits::Arb(mut s)) => {
        let (hi, overflow) = match o {
          Digits::Arb(mut o) => {
            let s_len = s.len();
            let o_len = o.len();
            let min_len = s_len.min(o_len);
            if o_len > s_len {
              mem::swap(&mut s, &mut o);
            }

            let (word_0, word_hi) = s.split_at_mut(min_len);
            (word_hi, carrying_add(word_0, &o[..min_len]))
          }

          Digits::Fix(o) => {
            if let Some((word_0, word_hi)) = s.split_first_mut() {
              let (a, overflow) = word_0.overflowing_add(o);
              *word_0 = a;
              (word_hi, overflow)
            } else {
              return Digits::Arb(s);
            }
          }
        };

        let carry = overflow && overflowing_add_word(hi, 1);
        push_carry(&mut s, carry as Word);
        Digits::from(s)
      }
    }
  }
}

impl Sub<Digits> for Digits {
  type Output = Digits;

  fn sub(self, o: Digits) -> Self::Output {
    match (self, o) {
      (Digits::Fix(lhs), Digits::Fix(rhs)) => {
        if let Some(sub) = lhs.checked_sub(rhs) {
          Digits::Fix(sub)
        } else {
          panic!("attempt to subtract with overflow")
        }
      }

      (Digits::Fix(_), Digits::Arb(_)) => {
        panic!("attempt to subtract with overflow")
      }

      (Digits::Arb(mut s), o) => {
        let (hi, borrow) = match o {
          Digits::Arb(o) => {
            let s_len = s.len();
            let o_len = o.len();

            if o_len > s_len {
              panic!("attempt to subtract with overflow")
            }

            let (words_lo, words_hi) = s.split_at_mut(o_len);
            (words_hi, borrowing_sub_lhs(words_lo, &o))
          }

          Digits::Fix(o) => {
            if let Some((word_0, words_hi)) = s.split_first_mut() {
              let (a, borrow) = word_0.overflowing_sub(o);
              *word_0 = a;
              (words_hi, borrow)
            } else {
              return Digits::Arb(s);
            }
          }
        };

        let borrow = borrow && borrowing_sub_word(hi, 1);
        if borrow {
          panic!("attempt to subtract with overflow")
        } else {
          Digits::from(s)
        }
      }
    }
  }
}

impl Mul<Digits> for Digits {
  type Output = Digits;

  fn mul(self, o: Digits) -> Self::Output {
    match (self, o) {
      (Digits::Fix(0), _) | (_, Digits::Fix(0)) => Digits::Fix(0),
      (Digits::Fix(1), o) | (o, Digits::Fix(1)) => o,

      (Digits::Fix(lhs), Digits::Fix(rhs)) => Digits::from_le_bytes(&(extend_word(lhs) * extend_word(rhs)).to_le_bytes()),

      (Digits::Arb(mut s), o) | (o, Digits::Arb(mut s)) => match o {
        Digits::Arb(mut o) => {
          let s_len = s.len();
          let o_len = o.len();
          let res_len = s_len + o_len;
          if o_len > s_len {
            mem::swap(&mut s, &mut o);
          }

          let mut mul = vec![0; res_len];
          carrying_mul_add(&mut mul, &s, &o);
          Digits::from(mul)
        }

        Digits::Fix(o) => {
          let carry = carrying_mul_word(&mut s, o, 0);
          push_carry(&mut s, carry);
          Digits::Arb(s)
        }
      },
    }
  }
}

impl Div<Digits> for Digits {
  type Output = Digits;

  fn div(self, o: Digits) -> Self::Output {
    match (self, o) {
      (_, Digits::Fix(0)) => panic!("attempt to divide by zero"),
      (o, Digits::Fix(1)) => o,

      (Digits::Fix(lhs), Digits::Fix(rhs)) => Digits::Fix(lhs.div(rhs)),
      (Digits::Fix(_), Digits::Arb(_)) => Digits::Fix(0),

      (Digits::Arb(mut s), o) => match o {
        Digits::Arb(mut o) => {
          let s_len = s.len();
          let o_len = o.len();

          if o_len > s_len {
            Digits::Fix(0)
          } else {
            if let Some(last) = o.last() {
              let shift = last.leading_zeros();
              let _rhs_carry = carrying_shl_word(&mut o, shift);
              let _lhs_carry = carrying_shl_word(&mut s, shift);
              if _lhs_carry != 0 {
                s.push(_lhs_carry);
              }
              let overflow = Normalizer::new(*o.last().unwrap()).remaining_div(
                &mut s, // > 1
                &o,
              );
              if overflow {
                s.push(1);
              }
              s.drain(..o_len);
            }
            Digits::from(s)
          }
        }

        Digits::Fix(o) => {
          let _ = remainding_div_word(&mut s, o);
          Digits::Arb(s)
        }
      },
    }
  }
}

impl Rem<Digits> for Digits {
  type Output = Digits;

  fn rem(self, o: Digits) -> Self::Output {
    match (self, o) {
      (_, Digits::Fix(0)) => panic!("attempt to divide by zero"),
      (_, Digits::Fix(1)) => Digits::Fix(0),
      (Digits::Fix(1), _) => Digits::Fix(1),

      (Digits::Fix(lhs), Digits::Fix(rhs)) => Digits::Fix(lhs.rem(rhs)),
      (Digits::Fix(word), Digits::Arb(_)) => Digits::Fix(word),

      (Digits::Arb(mut s), o) => match o {
        Digits::Arb(mut o) => {
          let s_len = s.len();
          let o_len = o.len();

          if o_len < s_len {
            Digits::from(s)
          } else {
            if let Some(last) = o.last() {
              let shift = last.leading_zeros();
              let _rhs_carry = carrying_shl_word(&mut o, shift);
              let _lhs_carry = carrying_shl_word(&mut s, shift);
              if _lhs_carry != 0 {
                s.push(_lhs_carry);
              }
              let overflow = Normalizer::new(*o.last().unwrap()).remaining_div(
                &mut s, // > 1
                &o,
              );
              if overflow {
                s.push(1);
              }
              o.copy_from_slice(&s[..o_len]);
              carrying_shr_word(&mut o, shift);
            }
            Digits::from(o)
          }
        }

        Digits::Fix(o) => {
          let r = remainding_div_word(&mut s, o);
          Digits::Fix(r)
        }
      },
    }
  }
}

impl Digits {
  pub(crate) fn div_rem(self, o: Digits) -> (Digits, Digits) {
    match (self, o) {
      (_, Digits::Fix(0)) => panic!("attempt to divide by zero"),
      (o, Digits::Fix(1)) => (o, Digits::Fix(0)),

      (Digits::Fix(lhs), Digits::Fix(rhs)) => (Digits::Fix(lhs.div(rhs)), Digits::Fix(lhs % rhs)),
      (Digits::Fix(word), Digits::Arb(_)) => (Digits::Fix(0), Digits::Fix(word)),

      (Digits::Arb(mut s), o) => match o {
        Digits::Arb(mut o) => {
          let s_len = s.len();
          let o_len = o.len();

          if o_len > s_len {
            (Digits::Fix(0), Digits::from(s))
          } else {
            if let Some(last) = o.last() {
              let shift = last.leading_zeros();
              let _rhs_carry = carrying_shl_word(&mut o, shift);
              let _lhs_carry = carrying_shl_word(&mut s, shift);
              if _lhs_carry != 0 {
                s.push(_lhs_carry);
              }
              let overflow = Normalizer::new(*o.last().unwrap()).remaining_div(
                &mut s, // > 1
                &o,
              );
              if overflow {
                s.push(1);
              }
              o.copy_from_slice(&s[..o_len]);
              carrying_shr_word(&mut o, shift);
              s.drain(..o_len);
            }
            (Digits::from(s), Digits::from(o))
          }
        }

        Digits::Fix(o) => {
          let r = remainding_div_word(&mut s, o);
          (Digits::Arb(s), Digits::Fix(r))
        }
      },
    }
  }
}

#[derive(Clone, Copy)]
struct Normalizer {
  div: Word,
  flr: Word,
}

impl Normalizer {
  const fn new(div: Word) -> Normalizer {
    let (flr, _) = split_dual(Dual::MAX / extend_word(div));
    Normalizer { div, flr }
  }

  const fn div_rem(&self, a: Dual) -> (Word, Word) {
    let (a_lo, a_hi) = split_dual(a);

    let (q0, q1) = split_dual(extend_word(self.flr) * extend_word(a_hi) + a);

    let q = q1.wrapping_add(1);
    let r = a_lo.wrapping_sub(q.wrapping_mul(self.div));

    let (_, decrease) = split_dual(extend_word(q0).wrapping_sub(extend_word(r)));
    let q = q.wrapping_add(decrease);
    let r = r.wrapping_add(decrease & self.div);

    let (_, increase) = split_dual(extend_word(r).wrapping_sub(extend_word(self.div)));
    let increase = !increase;
    let q = q.wrapping_sub(increase);
    let r = r.wrapping_sub(increase & self.div);

    (q, r)
  }

  #[inline]
  fn remainding_div_word(&self, lhs: &mut [Word], rhs: Word) -> Word {
    let shift = rhs.leading_zeros();
    let carry = carrying_shl_word(lhs, shift);
    let divquo = lhs.iter_mut().rev().fold(carry, |rem, word| {
      let (q, r) = self.div_rem(dual_word(*word, rem));
      *word = q;
      r
    });
    divquo >> shift
  }

  #[inline]
  fn remaining_div(&self, lhs: &mut [Word], rhs: &[Word]) -> bool {
    let rhs_len = rhs.len();
    let rhs0 = rhs[rhs_len - 1];
    let rhs1 = rhs[rhs_len - 2];
    let mut lhs_len = lhs.len();

    let lhs_rem = &mut lhs[lhs_len - rhs_len..];
    let overflow = cmp_digits(lhs_rem, rhs) >= Ordering::Equal;
    if overflow {
      borrowing_sub_lhs(lhs_rem, rhs);
    }

    while lhs_len > rhs_len {
      let lhs0 = lhs[lhs_len - 1];
      let lhs1 = lhs[lhs_len - 2];
      let lhs2 = lhs[lhs_len - 3];
      let lhs01 = dual_word(lhs1, lhs0);

      let mut div = if lhs0 < rhs0 {
        let (mut div, mut rem) = self.div_rem(lhs01);
        while extend_word(div) * extend_word(rhs1) > dual_word(lhs2, rem) {
          div -= 1;
          if let Some(rr) = rem.checked_add(rhs0) {
            rem = rr;
          } else {
            break;
          }
        }
        div
      } else {
        Word::MAX
      };

      let lhs_div = &mut lhs[lhs_len - 1 - rhs_len..lhs_len - 1];
      let borrow = borrowing_mul_sub(lhs_div, div, rhs);
      if borrow > lhs0 {
        div -= 1;
        let _ = carrying_add(lhs_div, rhs);
      }
      lhs_len -= 1;
      lhs[lhs_len] = div;
    }
    overflow
  }
}

impl BitOr<Digits> for Digits {
  type Output = Digits;

  fn bitor(self, o: Digits) -> Self::Output {
    match (self, o) {
      (Digits::Fix(lhs), Digits::Fix(rhs)) => Digits::Fix(lhs | rhs),

      (Digits::Arb(mut s), o) | (o, Digits::Arb(mut s)) => match o {
        Digits::Arb(mut o) => {
          let s_len = s.len();
          let o_len = o.len();
          if o_len > s_len {
            mem::swap(&mut s, &mut o);
          }

          for (l, r) in s.iter_mut().zip(o.iter()) {
            *l |= *r;
          }

          Digits::from(
            s, //.
          )
        }

        Digits::Fix(o) => {
          if let Some(first) = s.first_mut() {
            *first |= o;
          }

          Digits::from(s)
        }
      },
    }
  }
}

impl Shl<usize> for Digits {
  type Output = Digits;

  fn shl(self, o: usize) -> Self::Output {
    let shift_words = o / WORD_BITS;
    let shift_bits = (o % WORD_BITS) as u32;

    let mut s = match self {
      Digits::Fix(word) => {
        let (lo, hi) = split_dual(extend_word(word) << shift_bits);
        vec![lo, hi]
      }
      Digits::Arb(mut s) => {
        let carry = carrying_shl_word(&mut s, shift_bits);
        s.push(carry);
        s
      }
    };

    s.splice(..0, iter::repeat(0).take(shift_words));
    Digits::from(
      s, //.
    )
  }
}

impl Shr<usize> for Digits {
  type Output = Digits;

  fn shr(self, o: usize) -> Self::Output {
    match self {
      Digits::Fix(word) => Digits::Fix(word >> o),

      Digits::Arb(mut s) => {
        let shift_words = o / WORD_BITS;
        let shift_bits = (o % WORD_BITS) as u32;

        if shift_words >= s.len() {
          Digits::Fix(0)
        } else {
          s.drain(..shift_words);
          carrying_shr_word(&mut s, shift_bits);
          Digits::from(
            s, //.
          )
        }
      }
    }
  }
}

struct Basis {
  digits_per_word: usize,
  range_per_word: Word,
  norm: Normalizer,
}

impl Basis {
  const fn new(radix: u32) -> Basis {
    let mut digits_per_word = 0;
    let mut range_per_word: Word = 1;
    while let Some(range) = range_per_word.checked_mul(radix as Word) {
      digits_per_word += 1;
      range_per_word = range;
    }

    let shift = range_per_word.leading_zeros();
    let norm = Normalizer::new(range_per_word << shift);

    Basis {
      digits_per_word,
      range_per_word,
      norm,
    }
  }
}

/// An arbitrary number parsing error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
  InvalidDigit,
}

fn parse_word(src: &[u8], radix: u32) -> Result<Word, ParseError> {
  src.iter().try_fold(0, |acc, byte| {
    Ok(acc * (radix as Word) + (digit_from_utf8_byte(*byte, radix).ok_or(ParseError::InvalidDigit)? as Word))
    //.
  })
}

fn digit_from_utf8_byte(byte: u8, radix: u32) -> Option<u32> {
  let res = match byte {
    b'0'..=b'9' => (byte - b'0') as u32,
    b'a'..=b'z' => (byte - b'a') as u32 + 10,
    b'A'..=b'Z' => (byte - b'A') as u32 + 10,
    _ => return None,
  };
  if res < radix {
    Some(res)
  } else {
    None
  }
}

impl fmt::Display for Digits {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Digits::Fix(word) => {
        write!(f, "{word}")
      }

      Digits::Arb(array) => {
        let basis = Basis::new(10);

        let mut digits = array.clone();
        let mut groups = Array::new();

        let mut iter = (1..array.len()).rev();
        let mut next = iter.next();

        while let Some(i) = next {
          if digits[i] != 0 {
            let rem = basis.norm.remainding_div_word(&mut digits[..i + 1], basis.range_per_word);
            groups.push(rem);
          } else {
            next = iter.next()
          }
        }

        write!(f, "{}", digits[0])?;
        for word in groups.iter().rev() {
          write!(f, "{word:0digits$}", digits = basis.digits_per_word)?;
        }

        Ok(())
      }
    }
  }
}

#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub(crate) enum Sign {
  Negative,
  Positive,
}

impl Neg for Sign {
  type Output = Sign;

  #[inline]
  fn neg(self) -> Sign {
    match self {
      Sign::Positive => Sign::Negative,
      Sign::Negative => Sign::Positive,
    }
  }
}

impl Mul<Sign> for Sign {
  type Output = Sign;

  fn mul(self, rhs: Sign) -> Sign {
    if self.eq(&rhs) {
      Sign::Positive
    } else {
      Sign::Negative
    }
  }
}

impl From<Ordering> for Sign {
  fn from(ord: Ordering) -> Sign {
    if let Ordering::Greater | Ordering::Equal = ord {
      Sign::Positive
    } else {
      Sign::Negative
    }
  }
}

impl From<i32> for Sign {
  fn from(sgn: i32) -> Sign {
    if sgn >= 0 {
      Sign::Positive
    } else {
      Sign::Negative
    }
  }
}

impl Sign {
  #[inline]
  pub(crate) fn diff(lhs: Digits, rhs: Digits) -> (Sign, Digits) {
    let lhs_len = lhs.len();
    let rhs_len = rhs.len();
    let min_len = lhs_len.min(rhs_len);

    match (lhs, rhs) {
      (Digits::Fix(lhs), Digits::Fix(rhs)) => {
        let (val, overflow) = lhs.overflowing_sub(rhs);
        if overflow {
          (Sign::Negative, Digits::Fix(val.wrapping_neg()))
        } else {
          (Sign::Positive, Digits::Fix(val))
        }
      }

      (Digits::Arb(mut s), Digits::Fix(word)) | (Digits::Fix(word), Digits::Arb(mut s)) => {
        borrowing_sub_word(&mut s, word);
        (Sign::from(lhs_len.cmp(&rhs_len)), Digits::from(s))
      }

      (Digits::Arb(mut lhs), Digits::Arb(rhs)) => {
        let mut sgn = lhs_len.cmp(&rhs_len);
        match sgn {
          Ordering::Equal => {
            sgn = lhs.last().cmp(&rhs.last());
            match sgn {
              Ordering::Greater => {
                borrowing_sub_lhs(&mut lhs, &rhs);
              }

              Ordering::Less => {
                borrowing_sub_rhs(&rhs, &mut lhs);
              }

              Ordering::Equal => {
                lhs[lhs_len - 1] = 0;
                return Sign::diff(
                  lhs.into(), //.
                  rhs.into(),
                );
              }
            };
          }

          ord => {
            let (rhs_lo, rhs_hi) = rhs.split_at(min_len);
            lhs.extend(rhs_hi);
            let (lhs_lo, lhs_hi) = lhs.split_at_mut(min_len);

            let _ = if ord.is_lt() {
              borrowing_sub_rhs(
                rhs_lo, //.
                lhs_lo,
              )
            } else {
              borrowing_sub_lhs(
                lhs_lo, //.
                rhs_lo,
              )
            } && borrowing_sub_word(
              lhs_hi, //.
              1,
            );
          }
        };

        (
          Sign::from(sgn),
          Digits::from(
            lhs, //.
          ),
        )
      }
    }
  }
}

/// A trait describing the expression's behavior based on abstract algebra principles.
pub trait Theory: fmt::Debug {
  /// Abstract algebraic set notation.
  fn notation(&self) -> &str;
}

/// An abstract structure annotation.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub enum Structure {
  /// Abstract
  AS,
  /// Natural
  N,
  /// Integer
  Z,
  /// Rational
  Q,
  /// Real
  R,
  /// Complex
  C,
  /// Custom
  SR,
}
