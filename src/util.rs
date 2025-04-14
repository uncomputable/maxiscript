/// Similar to [`std::slice::split_last_chunk`], but replace missing elements with `None`.
#[allow(dead_code)]
pub const fn split_last_chunk<const N: usize, T>(s: &[T]) -> (&[T], [Option<&T>; N]) {
    let front = match s.split_last_chunk::<N>() {
        Some((front, _)) => front,
        None => &[],
    };
    let mut last_chunk: [Option<&T>; N] = [None; N];

    let mut i = 0;
    while i < N {
        let index = s.len().wrapping_sub(1).wrapping_sub(i);
        last_chunk[N - 1 - i] = match index < s.len() {
            true => Some(&s[index]),
            false => None,
        };
        i += 1;
    }

    (front, last_chunk)
}

/// Similar to [`std::slice::split_last_chunk`], but replace missing elements with `None`.
pub const fn split_last_chunk2<const N: usize, T>(
    s: &[Option<T>],
) -> (&[Option<T>], [Option<&T>; N]) {
    let front = match s.split_last_chunk::<N>() {
        Some((front, _)) => front,
        None => &[],
    };
    let mut last_chunk: [Option<&T>; N] = [None; N];

    let mut i = 0;
    while i < N {
        let index = s.len().wrapping_sub(1).wrapping_sub(i);
        last_chunk[N - 1 - i] = match index < s.len() {
            true => s[index].as_ref(),
            false => None,
        };
        i += 1;
    }

    (front, last_chunk)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_last_chunk() {
        // Slice length 0
        assert_eq!((&[] as &[_], []), split_last_chunk::<0, usize>(&[]));
        assert_eq!((&[] as &[_], [None]), split_last_chunk::<1, usize>(&[]));
        // Slice length 1
        assert_eq!((&[0] as &[_], []), split_last_chunk::<0, _>(&[0]));
        assert_eq!((&[] as &[_], [Some(&0)]), split_last_chunk::<1, _>(&[0]));
        assert_eq!(
            (&[] as &[_], [None, Some(&0)]),
            split_last_chunk::<2, _>(&[0])
        );
        assert_eq!(
            (&[] as &[_], [None, None, Some(&0)]),
            split_last_chunk::<3, _>(&[0])
        );
        // Slice length 2
        assert_eq!((&[0, 1] as &[_], []), split_last_chunk::<0, _>(&[0, 1]));
        assert_eq!(
            (&[0] as &[_], [Some(&1)]),
            split_last_chunk::<1, _>(&[0, 1])
        );
        assert_eq!(
            (&[] as &[_], [Some(&0), Some(&1)]),
            split_last_chunk::<2, _>(&[0, 1])
        );
        assert_eq!(
            (&[] as &[_], [None, Some(&0), Some(&1)]),
            split_last_chunk::<3, _>(&[0, 1])
        );
        assert_eq!(
            (&[] as &[_], [None, None, Some(&0), Some(&1)]),
            split_last_chunk::<4, _>(&[0, 1])
        );
    }
}
