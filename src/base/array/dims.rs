use std::cmp;
use std::iter;
use std::ops::Index;

pub trait Dims {
  fn size(&self) -> usize;
  fn order(&self) -> usize;
  fn shape(&self) -> &[usize];
  fn local(&self) -> (&[usize], usize);

  fn from_index(&self, select: &[usize]) -> usize;
  fn from_slice(&self, select: &[Slice]) -> Self;
}

pub struct Slice {
  pub start: usize,
  pub end: usize,
  pub step: usize,
}

impl Slice {
  pub const fn all() -> Slice {
    Slice {
      //.
      start: 0,
      end: usize::MAX,
      step: 1,
    }
  }

  pub const fn one(idx: usize) -> Slice {
    Slice {
      //.
      start: idx,
      end: idx + 1,
      step: 1,
    }
  }

  // newaxis
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Dense {
  dim: Vec<usize>,
  loc: Vec<usize>,
  ext: usize,
  len: usize,
}

impl Dense {
  pub fn new(shape: &[usize]) -> Dense {
    let mut loc: Vec<_> = iter::once(1)
      .chain(
        shape //.
          .iter()
          .rev()
          .take(shape.len() - 1)
          .scan(1, |s, &d| {
            *s *= d;
            Some(*s)
          }),
      )
      .collect();
    loc.reverse();

    let len = shape.iter().product();
    let ext = 0;

    Dense {
      //.
      dim: shape.to_vec(),
      loc,
      ext,
      len,
    }
  }
}

impl Dims for Dense {
  fn size(&self) -> usize { self.len }
  fn order(&self) -> usize { self.dim.len() }
  fn shape(&self) -> &[usize] { &self.dim }
  fn local(&self) -> (&[usize], usize) { (&self.loc, self.ext) }

  fn from_index(&self, select: &[usize]) -> usize { select.iter().zip(self.loc.iter()).fold(self.ext, |pos, (i, s)| pos + i * s) }

  fn from_slice(&self, select: &[Slice]) -> Self {
    let mut len = 1;
    let mut ext = self.ext;

    let (dim, loc) = select
      .iter()
      .chain(iter::repeat(
        &Slice::all(), //.
      ))
      .zip(self.loc.iter().zip(self.dim.iter()))
      .map(|(idx, (l, s))| {
        let ns = (cmp::min(&idx.end, s) - cmp::min(&idx.start, s) + idx.step - 1) / idx.step;
        let nl = *l * idx.step;

        ext += *l * idx.start;
        len *= ns;
        (ns, nl)
      })
      .filter(|(ns, _)| ns != &1)
      .unzip();

    Dense {
      //.
      dim,
      loc,
      ext,
      len,
    }
  }
}

impl Index<usize> for Dense {
  type Output = usize;
  fn index(&self, idx: usize) -> &Self::Output { &self.dim[idx] }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Sparse {
  //.
}
