use std::mem;

pub trait Data: Clone {
  type Elem;

  fn get(&self, idx: usize) -> &Self::Elem;
  fn get_mut(&mut self, idx: usize) -> &mut Self::Elem;

  fn resize(&mut self, new_len: usize, value: Self::Elem);
  fn size_of(&self) -> usize;
}

impl<T> Data for Vec<T>
where
  T: Clone,
{
  type Elem = T;

  fn get(&self, idx: usize) -> &Self::Elem { &self[idx] }
  fn get_mut(&mut self, idx: usize) -> &mut Self::Elem { &mut self[idx] }

  fn resize(&mut self, new_len: usize, value: Self::Elem) { self.resize(new_len, value) }
  fn size_of(&self) -> usize {
    self.capacity() * mem::size_of::<T>() //.
  }
}
