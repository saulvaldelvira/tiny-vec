/* Dumb program to show one of the uses of the TinyVec.
 *
 * Sometimes you need to collect some elements (e.g. Collecting an
 * iterator), temporarily. But you are not going to store them for a
 * long time.
 * The naive approach is to use a Vec. The problem is that when we are
 * dealing with an small amount of elements, a vec can be overkill.
 *
 * In the example bellow, we perform 2 runs. One with the default stack
 * size for the vector. This is, using only the minimun required stack size.
 * 24 bytes. 8 bytes for a poiter, 8 for the length and 8 for capacity.
 *
 * By using tiny-vec, we managed to avoid memory allocations in two cases.
 *
 * The second run uses a slightly higher stack buffer (32 bytes), and only
 * needs to allocate memory on 1 of the iterations.
 *
 * I think is really useful, and amazing! Specially the first case, since it
 * doesn't even use extra stack space, but avoids allocations for iterators
 * with up to 8 elements.
 *
 * NOTE: I know this is a dumb example, since all those operations could've been
 * done without any kind of vector, just maping the iterator. But the TinyVec has
 * practical applications... I PROMISE!
 */

use core::mem;
use core::ops::Range;

use tiny_vec::{TinyVec};

fn mutate_slice(slice: &mut [u16]) {
    for e in slice {
        *e *= 2;
    }
}

fn process_iter<const N: usize>(range: Range<u16>) {
    let mut collected: TinyVec<u16, N> = range.clone().collect();
    mutate_slice(&mut collected);
    println!("\n  Range: {range:?} ({} elements)", range.end - range.start);
    println!("  Result: {collected:?}\n  Used heap: {}", !collected.lives_on_stack());
}

fn run<const N: usize>() {
    process_iter::<N>(0..10);
    process_iter::<N>(3..11);
    process_iter::<N>(0..30);
    process_iter::<N>(4..7);
}

pub fn main() {
    const DEF: usize = tiny_vec::n_elements_for_stack::<u16>();
    let stack_size: usize = mem::size_of::<TinyVec<u16, DEF>>();
    println!("Using a TinyVec with the default stack size ({DEF}). (Size = {stack_size})");
    run::<DEF>();

    let stack_size: usize = mem::size_of::<TinyVec<u16, 10>>();
    println!("\nUsing a TinyVec with a custom stack size of 10. (Size = {stack_size})");
    run::<10>();
}
