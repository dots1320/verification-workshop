# Bonus answers

Name(s): Yin ZeYan (GitHub: dots1320)

Tools: OpenJML 21.0.29 and JBMC 6.11.0.

## 1. Composite

Q: Which part of the invariant breaks, after which calls? What is wrong in `update`?

I checked that `value` is the maximum of `initValue` and the direct children's values. `maxChild` must be null exactly when `value == initValue`. Otherwise it must be a direct child with the same value. I also kept the parent pointer checks.

For example, let A, B and C start with values 0, 1 and 2. After `A.addChild(B)` and `B.addChild(C)`, the update reaches A. The original `parent.update(c)` passes C to A, so A's `maxChild` becomes its grandchild. This breaks the direct child requirement. The counterexample at K = 4 has this structure and fails `hasMaxChild`.

Changing the call to `parent.update(this)` fixes it: each node passes itself to its own parent. The original version failed at K = 4 and 5, and the fixed version passed both.

Q: Why does JBMC need K = 4 to find a bug that needs two calls?

The bound applies to every loop. The initialization loop creates three nodes and needs an exit check, so K = 4 is needed before the later checks can run. At K = 2 and 3, initialization was cut off and no SAT formula was generated. Those SUCCESSFUL results did not check the tree invariant.

Q: How large is the formula? What would you need to verify `Composite` with OpenJML?

These results use the original bug, the single-node precondition and the completed local invariant checks:

| K | SAT variables | SAT clauses | Solver time (s) | Result |
| --- | ---: | ---: | ---: | --- |
| 2 | No formula | No formula | - | Initialization cut off |
| 3 | No formula | No formula | - | Initialization cut off |
| 4 | 136022 | 334704 | 3.370900 | FAILED |
| 5 | 193043 | 498099 | 4.260529 | FAILED |

This is much larger than Max, which had about 7646 variables. JBMC has to encode objects, references, aliasing, parent-child links and call histories. It is not larger than every other example in every measure: SumX at K = 1001 had about 666136 clauses. The size depends on the model and bound.

An OpenJML proof for trees of any size would need specifications for reachability, acyclicity, parent-child links and cached maximum values. It would also need frame conditions for the nodes that can change, a contract for recursive `update`, and a termination argument. Updating ancestors must preserve their invariants too. Checking three nodes does not establish this general result.

Q: What goes wrong when subtrees are allowed?

Removing only `c.firstChild == null` allows cycles. For example, `B.addChild(C)` followed by `C.addChild(B)` connects an ancestor under its descendant. If the cached values stay the same, the local checks can still pass. They did pass at K = 5, but adding an acyclicity check found the cycle at the same bound.

My implementation allows subtrees but requires `c` to be a root and rejects it if it is on `this` node's ancestor chain. The harness only makes legal additions, including the original single-node cases. The checker follows at most NODES parent links and asserts that it reaches null, so a cycle fails an explicit assertion.

The subtree version gave these results:

| K | SAT variables | SAT clauses | Solver time (s) | Result |
| --- | ---: | ---: | ---: | --- |
| 4 | 176330 | 444730 | 4.901620 | SUCCESSFUL |
| 5 | 253109 | 668824 | 5.406480 | SUCCESSFUL |

Separate deterministic checks with unwinding assertions also passed for attaching a whole subtree and throwing `IllegalArgumentException` on a cycle request. The JBMC result still covers only three nodes within the chosen bounds.

## 2. SafeLock for any number of events

Q: Why does OpenJML think `failed++` may overflow?

OpenJML checks each method separately. Setting `failed = 0` in the constructor does not tell it the range at every later method entry. Without a class invariant, it cannot rule out a value near the int limit and reports `ArithmeticOperationRange`.

I used these invariants:

```java
//@ private invariant 0 <= failed && failed <= MAX_ATTEMPTS;
//@ private invariant (state == State.BLOCKED) <==> (failed == MAX_ATTEMPTS);
//@ private invariant state == State.OPEN ==> failed == 0;
```

The increment only happens in LOCKED. The invariants imply that `failed` is at most 2 there, so incrementing it is safe. The state changes preserve the invariants, and `./esc plus/SafeLock.java` passes.

Q: Does your invariant catch the bug of homework plus, exercise 5? What does this proof give you that JBMC did not?

Yes. With the original `close` bug, OpenJML reports `InvariantExit`: closing a BLOCKED lock resets `failed` from 3 to 0 but leaves the state BLOCKED. This breaks the relation between the state and counter.

The inductive proof holds for any finite number of calls, since the invariants hold initially and every legal call preserves them. It proves these state relations and the related arithmetic safety without a fixed event bound. The bounded JBMC runs do not give that result.

These invariants do not record the full history of wrong PIN entries. Proving all the history properties in the two harnesses for any number of events would also need suitable method contracts or ghost state.
