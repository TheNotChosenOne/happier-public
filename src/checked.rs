use alloc::vec::Vec;

#[inline(always)]
pub(crate) fn unchecked_mut<T>(slice: &mut [T], index: usize) -> &mut T {
    &mut slice[index]
}

#[inline(always)]
pub(crate) fn unchecked_get<T>(slice: &[T], index: usize) -> &T {
    &slice[index]
}

#[inline(always)]
pub(crate) fn unchecked_split<T>(slice: &[T], mid: usize) -> (&[T], &[T]) {
    slice.split_at(mid)
}

#[inline(always)]
pub(crate) fn unchecked_unwrap<T>(option: Option<T>) -> T {
    option.unwrap()
}

#[inline(always)]
pub(crate) fn unchecked_ok<T>(result: Result<T, impl core::fmt::Debug>) -> T {
    result.unwrap()
}

#[inline(always)]
pub(crate) fn unchecked_err<T>(result: Result<impl core::fmt::Debug, T>) -> T {
    result.unwrap_err()
}

#[inline(always)]
pub(crate) fn unchecked_shift_right<T: Copy>(slice: &mut [T], start: usize, len: usize) {
    slice.copy_within(start..start + len, start + 1);
}

#[inline(always)]
pub(crate) fn unchecked_shift_left<T: Copy>(slice: &mut [T], start: usize, len: usize) {
    slice.copy_within(start + 1..=start + len, start);
}

/// Swaps the first match in `start..end` into `target`.
#[inline(always)]
pub(crate) fn unchecked_find_swap<T: Copy>(
    slice: &mut [T],
    start: usize,
    end: usize,
    target: usize,
    matches: impl Fn(T) -> bool,
) -> T {
    let index = start + unchecked_unwrap(slice[start..end].iter().position(|&x| matches(x)));
    slice.swap(index, target);
    slice[target]
}

pub(crate) fn unchecked_remove<T>(slice: &mut Vec<T>, condition: impl Fn(&T) -> bool) -> T {
    let position = slice.iter().position(condition);
    let position = unchecked_unwrap(position);
    slice.swap_remove(position)
}
