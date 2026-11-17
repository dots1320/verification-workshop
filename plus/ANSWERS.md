# Homework plus: answers

Name(s): Yin ZeYan (GitHub: dots1320)

Tools: OpenJML 21.0.29 and JBMC 6.11.0.

### 1. Invariants from an LLM

| method | LLM | rounds | mistakes | final invariants by |
| --- | --- | --- | --- | --- |
| count | Codex | 1 | None reported | Codex, checked by OpenJML |
| reverse | Codex | 1 | None reported | Codex, checked by OpenJML |
| isqrt | Codex | 1 | None reported | Codex, checked by OpenJML |
| dutchFlag | Codex | 1 | None reported | Codex, checked by OpenJML |

For `count`, `c` is the number of matches in the scanned prefix, with `0 <= c <= i`.
For `reverse`, the two ends are reversed, the middle is unchanged, and the indices stay symmetric.
For `isqrt`, `r*r <= n` and `0 <= r <= 1000` keep the calculation safe.
For `dutchFlag`, the invariants describe the index order and the sections containing 0, 1 and 2.
All four methods passed on the first round, both separately and as a whole file.

Q: Why is it safe to use invariants written by an LLM here, even if the LLM is often wrong?

The LLM suggests invariants, and OpenJML checks that they hold initially, survive each iteration,
and imply the postcondition. It also checks safety and the decreasing measure. A wrong suggestion
should fail verification. The result still depends on the contracts describing the intended behavior
and on trusting the verification tool.

### 2. The Zune bug

Q: `--unwind 31 --no-unwinding-assertions` says SUCCESSFUL. Does that mean `yearOf` is correct for every day it checked?

No. It checks executions that reach the assertions within the bound. Longer or infinite executions
are cut off. A returned year being in range does not show that every input returns or that the year is correct.

Q: What does JBMC report without `--no-unwinding-assertions`? Is K too small, or is something else wrong?

JBMC reports an unwinding assertion failure. At K=31, one input is `days=1827`, which gets stuck
at `year=1984, days=366`. K=60 still fails; another counterexample is `days=366`, which gets stuck
in 1980. The problem is an infinite loop.

Q: What is wrong with the loop? Which date froze the Zune?

The loop continues while `days > 365`, but the leap-year branch only makes progress when
`days > 366`. With exactly 366 days left in a leap year, nothing changes.
The Zune froze on December 31, 2008, day 10593 counting January 1, 1980 as day 1.
When the loop reaches 2008, it has exactly 366 days left.

The fix calculates the length of the current year. If the remaining days fit in that year, it stops;
otherwise it subtracts that year's length and advances the year.

Q: With your fix, what is the smallest K that gives VERIFICATION SUCCESSFUL with unwinding assertions? What exactly has been proved?

The smallest bound is K=30. K=29 fails an unwinding assertion, and both harnesses pass at K=30.
The loop may subtract 29 complete years and then needs its exit check.

This covers `days=1..10950`: the method terminates, returns a year in range, and the stronger harness
shows that the day belongs to that year. Since `MAX_DAYS=365*30` leaves out leap days, the range ends
on December 23, 2009. It does not cover 30 complete calendar years or arbitrary integer inputs.

Q: A colleague changes `days > 366` to `days >= 366`. Which harness notices, and why?

`yearOfInRange` still passes, but `yearOfIsRight` fails. For `days=366`, the answer should be 1980.
The change subtracts 366, leaves zero days, and returns 1981. This is still in the allowed year range,
so the weaker harness misses it.

The stronger harness sets `before=daysBefore(year)` and checks
`before < days && days <= before + daysInYear`, which catches the wrong year.

Q (★): Why does `./esc` say OK on the original? What changes with `decreases`?

The original proof only establishes partial correctness: if the method returns, the result is in range.
It does not prove termination. Adding `decreases days` gives a `LoopDecreases` failure on the original
code because the loop makes no progress with 366 days left in a leap year. The fixed version passes
with this decreasing measure.

### 3. Range

Q: Why does `size()` not verify? Give concrete values.

`lo <= hi` does not guarantee that the size fits in an `int`. Both `hi-lo` and the following `+1`
can overflow. OpenJML reports `ArithmeticOperationRange` and `Postcondition` failures.
For example, `lo=-2147483648, hi=2147483647` gives a size of 4294967296, which cannot fit in an `int`.

Q: Compare JBMC's counterexample with your answer above.

JBMC found `lo=-633754814, hi=1972821695`. The correct size is 2606576510, but the original method
returns -1688390786. This is the same overflow problem.

The fix keeps the original `ensures`, changes the return type to `long`, and uses
`return (long) hi - lo + 1;`. Casting before the subtraction makes the calculation use `long`.
OpenJML and `RangeCheck.size --unwind 1` both pass without narrowing the input range.

### 4. StackAr

Q: Which tool reports your bug, and how? Could a bug get past OpenJML but not JBMC, or the other way around?

The stack uses an array and `top`. An empty stack has `top=-1`; a full stack has `top=capacity-1`.
The class invariant bounds `top`, the method contracts describe the results and changes to `top`,
and `assignable` limits which locations can change. Capacity zero is allowed and is both empty and full.
The implementation passes OpenJML and the given JBMC check at K=5.

Removing `top--` from `pop` makes both tools report a bug. OpenJML fails the `pop` postcondition
because `top` does not decrease. JBMC fails `s.size() == n`: after a push and pop on a capacity-one
stack, the model size decreases but the actual size does not.

A weak OpenJML contract may miss behavior that the JBMC model checks. In the other direction,
a small JBMC bound may miss a bug requiring a longer sequence or a larger stack, while OpenJML
can detect the contract violation.

### 5. SafeLock

Q: Smallest K that finds a bug? Which sequence of events? What is wrong in the code?

K=1..4 passed on the original version. The smallest bound that finds the bug is K=5:

```text
wrong PIN -> wrong PIN -> Close -> wrong PIN -> correct PIN
```

`Close` resets `failed` even when the lock is already LOCKED. This sequence has three wrong PINs
without a successful PIN or admin reset, but the counter only records one. A correct PIN can then
open the door, violating the harness property. The fix moves `failed=0` inside the `state==OPEN`
branch, so closing a locked or blocked door does not clear the counter.

Q: Formula size and time for K = 8, 10, 12.

These measurements use the fixed code and the original Property 1 with `--no-unwinding-assertions`:

| K | SAT variables | SAT clauses | Solver time (s) | Total time (s) | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| 8 | 46050 | 68865 | 0.181350 | 0.809728 | SUCCESSFUL |
| 10 | 56941 | 87971 | 0.354194 | 1.042682 | SUCCESSFUL |
| 12 | 67836 | 107563 | 0.669870 | 1.342203 | SUCCESSFUL |

Solver time is reported by JBMC. Total time includes compilation and the script, and depends on machine load.
The new `onlyAdminUnblocks` harness also passes at K=8 and K=12. It checks that leaving BLOCKED
requires an admin reset with the correct code, without adding restrictions on `pin` or `adminCode`.

Q: Does SUCCESSFUL with K = 12 mean the property holds for every sequence? Can unwinding assertions help?

No. It only rules out counterexamples within the bound. The event loop uses `nondetBoolean`
and can run for any number of iterations, so no finite K exhausts it. Enabling unwinding assertions
fails at the harness loop, and increasing K cannot remove this issue. The bonus uses inductive
invariants to prove state properties without a fixed event bound.
