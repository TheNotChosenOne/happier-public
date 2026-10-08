use alloc::vec::Vec;

#[inline(always)]
pub(crate) fn unchecked_mut<T>(slice: &mut [T], index: usize) -> &mut T {
    debug_assert!(index < slice.len());
    unsafe { slice.get_unchecked_mut(index) }
}

#[inline(always)]
pub(crate) fn unchecked_get<T>(slice: &[T], index: usize) -> &T {
    debug_assert!(index < slice.len());
    unsafe { slice.get_unchecked(index) }
}

#[inline(always)]
pub(crate) fn unchecked_split<T>(slice: &[T], mid: usize) -> (&[T], &[T]) {
    debug_assert!(mid <= slice.len());
    unsafe { slice.split_at_unchecked(mid) }
}

#[inline(always)]
pub(crate) fn unchecked_unwrap<T>(option: Option<T>) -> T {
    debug_assert!(option.is_some());
    unsafe { option.unwrap_unchecked() }
}

#[inline(always)]
pub(crate) fn unchecked_ok<T>(result: Result<T, impl core::fmt::Debug>) -> T {
    debug_assert!(result.is_ok());
    unsafe { result.unwrap_unchecked() }
}

#[inline(always)]
pub(crate) fn unchecked_err<T>(result: Result<impl core::fmt::Debug, T>) -> T {
    debug_assert!(result.is_err());
    unsafe { result.unwrap_err_unchecked() }
}

#[inline(always)]
pub(crate) fn unchecked_shift_right<T: Copy>(slice: &mut [T], start: usize, len: usize) {
    debug_assert!(start + len < slice.len());
    if cfg!(feature = "unchecked-move") {
        unsafe {
            let ptr = slice.as_mut_ptr().add(start);
            core::ptr::copy(ptr, ptr.add(1), len);
        }
    } else {
        unsafe { slice.get_unchecked_mut(start..=start + len) }.copy_within(0..len, 1);
    }
}

#[inline(always)]
pub(crate) fn unchecked_shift_left<T: Copy>(slice: &mut [T], start: usize, len: usize) {
    debug_assert!(start + len < slice.len());
    if cfg!(feature = "unchecked-move") {
        unsafe {
            let ptr = slice.as_mut_ptr().add(start);
            core::ptr::copy(ptr.add(1), ptr, len);
        }
    } else {
        unsafe { slice.get_unchecked_mut(start..=start + len) }.copy_within(1..=len, 0);
    }
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
    debug_assert!(end <= slice.len());
    debug_assert!(target < slice.len());
    let ptr = slice.as_mut_ptr();
    let mut index = start;
    while index < end {
        if matches(unsafe { *ptr.add(index) }) {
            break;
        }
        index += 1;
    }
    debug_assert!(index < end);
    unsafe {
        let found = *ptr.add(index);
        *ptr.add(index) = *ptr.add(target);
        *ptr.add(target) = found;
        found
    }
}

pub(crate) fn unchecked_remove<T>(slice: &mut Vec<T>, condition: impl Fn(&T) -> bool) -> T {
    let position = slice.iter().position(condition);
    let position = unchecked_unwrap(position);
    slice.swap_remove(position)
}
