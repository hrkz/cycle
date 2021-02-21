mod data;
mod dims;
mod iters;

use std::fmt;
use std::iter;
use std::sync::Arc;

pub use data::*;
pub use dims::*;

pub type Array<T> = ArrayBase<Vec<T>, Dense>;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ArrayBase<S, D> {
  data: Arc<S>,
  dims: D,
}

impl<S, D> ArrayBase<S, D>
where
  S: Data,
  D: Dims,
{
  pub fn size(&self) -> usize { self.dims.size() }
  pub fn order(&self) -> usize { self.dims.order() }
  pub fn shape(&self) -> &[usize] { self.dims.shape() }

  pub fn is_vector(&self) -> bool { self.order() == 1 }
  pub fn is_matrix(&self) -> bool { self.order() == 2 }
  pub fn is_tensor(&self) -> bool { self.order() >= 3 }

  pub fn is_balanced(&self) -> bool {
    self
      .shape()
      //.
      .iter()
      .skip(1)
      .zip(iter::repeat(self.shape().first().unwrap_or(&0)))
      .all(|(d, f)| d == f)
  }

  pub fn get(&self, idx: &[usize]) -> &S::Elem { self.data.get(self.dims.from_index(idx)) }
  pub fn get_mut(&mut self, idx: &[usize]) -> &mut S::Elem { Arc::make_mut(&mut self.data).get_mut(self.dims.from_index(idx)) }

  pub fn slice(&self, idx: &[Slice]) -> ArrayBase<S, D> {
    let data = self.data.clone();
    let dims = self.dims.from_slice(idx);

    ArrayBase {
      //.
      data,
      dims,
    }
  }
}

fn format_array_inner(
  //.
  fmt: &mut fmt::Formatter<'_>,
  len: usize,
  lim: usize,
  sep: &str,
  ell: &str,
  fmt_idx: &mut dyn FnMut(&mut fmt::Formatter<'_>, usize) -> fmt::Result,
) -> fmt::Result {
  if len <= lim {
    fmt_idx(fmt, 0).and(
      (1..len) //.
        .try_for_each(|i| fmt.write_str(sep).and(fmt_idx(fmt, i))),
    )
  } else {
    let edge = lim / 2;
    let rest = len - edge;
    fmt_idx(fmt, 0)
      .and(
        (1..edge) //.
          .try_for_each(|i| fmt.write_str(sep).and(fmt_idx(fmt, i))),
      )
      .and(fmt.write_str(sep))
      .and(fmt.write_str(ell))
      .and(
        (rest..len) //.
          .try_for_each(|i| fmt.write_str(sep).and(fmt_idx(fmt, i))),
      )
  }
}

fn format_array<T, S, D>(
  //.
  arr: &ArrayBase<S, D>,
  fmt: &mut fmt::Formatter<'_>,
  sep: &str,
  ell: &str,
  cnt: usize,
  depth: usize,
  fmt_elem: &mut dyn FnMut(&mut fmt::Formatter<'_>, &T) -> fmt::Result,
) -> fmt::Result
where
  T: fmt::Display,
  S: Data<Elem = T>,
  D: Dims,
{
  match arr.shape() {
    // 0-d
    [] => fmt_elem(fmt, arr.get(&[]))?,
    // 1-d
    [len] => {
      fmt.write_str("[")?;
      format_array_inner(fmt, *len, cnt, sep, ell, &mut |fmt, idx| fmt_elem(fmt, arr.get(&[idx])))?;
      fmt.write_str("]")?;
    }
    // N-d
    shape => {
      let dim_sep = format!(",\n{}{}", "\n".repeat(shape.len() - 2), " ".repeat(depth + 1));

      fmt.write_str("[")?;
      format_array_inner(fmt, arr.shape()[0], cnt, &dim_sep, ell, &mut |fmt, idx| {
        format_array(
          &arr.slice(&[Slice::one(idx)]),
          fmt,
          sep,
          ell,
          cnt,
          depth + 1,
          fmt_elem,
          //.
        )
      })?;
      fmt.write_str("]")?;
    }
  }

  Ok(())
}

impl<T, S, D> fmt::Display for ArrayBase<S, D>
where
  T: fmt::Display,
  S: Data<Elem = T>,
  D: Dims,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { format_array(self, f, ", ", "...", 5, 0, &mut |f, elem| write!(f, "{:.p$}", elem, p = f.precision().unwrap_or(3))) }
}

impl<T: Clone> Array<T> {
  pub fn from_elem(shape: &[usize], elem: T) -> Array<T> { Array::from_vec(shape, vec![elem; shape.iter().product()]) }

  pub fn from_vec(shape: &[usize], values: Vec<T>) -> Array<T> {
    let data = Arc::new(values);
    let dims = Dense::new(shape);

    Array {
      //.
      data,
      dims,
    }
  }

  pub fn unpack(&self) -> (&[T], &[usize], &[usize]) {
    let (dim, (loc, ext)) = (self.dims.shape(), self.dims.local());
    // Unwrap dense array
    // Array at extended position
    // slice
    // shape
    // stride
    (
      &self.data[ext..], //.
      dim,
      loc,
    )
  }

  pub fn unpack_mut(&mut self) -> (&mut [T], &[usize], &[usize]) {
    let (dim, (loc, ext)) = (self.dims.shape(), self.dims.local());
    // Unwrap mutable dense array
    // Array at extended position
    // mut slice
    // shape
    // stride
    (
      &mut Arc::make_mut(&mut self.data)[ext..], //.
      dim,
      loc,
    )
  }
}
