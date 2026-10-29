//! Ferrum native recursion checkpoints; see [PLAN.md](../../../../PLAN.md).
//! Same-thread stack checkpoints for native recursive walkers.
//! This does not bound total recursion memory or make recursive drops iterative.

// Unoptimized executor frames can exceed 80 KiB. Reserve room for several
// intervening source rules and diagnostic calls before the next checkpoint.
const RED_ZONE: usize = 2 * 1024 * 1024;
const SEGMENT_SIZE: usize = 16 * 1024 * 1024;

#[inline(never)]
pub fn with_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(RED_ZONE, SEGMENT_SIZE, f)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::RefCell, rc::Rc, thread};

    struct Guard(Rc<RefCell<Vec<u8>>>, u8, thread::ThreadId);
    impl Drop for Guard {
        fn drop(&mut self) {
            assert_eq!(thread::current().id(), self.2);
            self.0.borrow_mut().push(self.1);
        }
    }

    #[test]
    fn grown_stack_keeps_thread_and_unwinds_borrowed_guards_once() {
        thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let owner = thread::current().id();
                let drops = Rc::new(RefCell::new(Vec::new()));
                let before = stacker::remaining_stack()
                    .expect("stack size available on supported test target");
                assert!(before < RED_ZONE);
                let returned: Result<(), &'static str> = with_stack(|| {
                    assert_eq!(thread::current().id(), owner);
                    assert!(stacker::remaining_stack().unwrap() > RED_ZONE);
                    let _first = Guard(drops.clone(), 1, owner);
                    let _second = Guard(drops.clone(), 2, owner);
                    Err("source error")
                });
                assert_eq!(returned, Err("source error"));
                assert_eq!(*drops.borrow(), vec![2, 1]);
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    with_stack(|| {
                        let _guard = Guard(drops.clone(), 3, owner);
                        std::panic::panic_any(42_u32);
                    });
                }));
                assert_eq!(*result.unwrap_err().downcast::<u32>().unwrap(), 42);
                assert_eq!(*drops.borrow(), vec![2, 1, 3]);
                assert!(stacker::remaining_stack().unwrap() < RED_ZONE);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
