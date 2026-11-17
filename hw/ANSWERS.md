# Homework answers

Name(s): Yin ZeYan (GitHub: dots1320)

Tools: OpenJML 21.0.29, JBMC 6.11.0, Java 21.0.4.

## OpenJML

### 1. Absolute

Q: What does OpenJML complain about before you write a contract, and for which input?

OpenJML reports `ArithmeticOperationRange: int negation` at `return -n;`.
The problem is `n = Integer.MIN_VALUE`, or -2147483648. Its absolute value is
2147483648, which does not fit in an int. Java wraps around and returns -2147483648.

Q: Which `requires` did you need, and why? Could you avoid it by changing the `ensures`?

I used `requires n > Integer.MIN_VALUE;` to exclude that input. The postconditions
say the result is non-negative and equals either `n` or `-n`.

Allowing a negative result for `Integer.MIN_VALUE` would weaken the meaning of
absolute value. It also does not remove OpenJML's overflow check: with safe
arithmetic, the negation still fails even if I weaken `ensures`. To keep the
non-negative result, I need this precondition or a wider return type and a changed
implementation.

### 2. SumX

Q: Which proof obligations fail? Is the program wrong?

With only `0 <= i && i <= x`, OpenJML cannot prove the postcondition or that
`s = s + i` avoids overflow. The program is correct for `0 <= x && x <= 1000`,
but the invariant says nothing about the value of `s`.

I added the relationship between the sum and the loop counter:

```java
//@ loop_invariant 0 <= i && i <= x;
//@ loop_invariant s == i * (i + 1) / 2;
//@ decreases x - i;
```

The sum starts at 0, and each iteration preserves this relationship by adding
the new value of `i`. At the end, `i == x`, so the postcondition follows.
The decreasing value `x - i` proves termination.

Q: Largest N for which `x <= N` verifies? What happens with N + 1, and why?

The largest bound I found was N = 65535:

```text
65535 * 65536 / 2 = 2147450880 <= Integer.MAX_VALUE
65536 * 65537 / 2 = 2147516416 >  Integer.MAX_VALUE
```

At 65536, OpenJML reports `ArithmeticOperationRange` for the addition and a
`LoopInvariant` failure. The last addition can overflow, so the sum no longer
matches the mathematical formula.

JML uses mathematical integers for these specification expressions, so the
intermediate multiplication in the specification does not limit N to 46340.
I put the precondition back to `x <= 1000` for exercise 6.

### 3. Max

Q: Is the remaining failure caused by your invariants or by the code? (Your hypothesis.)

I used these invariants with the original loop condition `i < a.length - 1`:

```java
//@ loop_invariant 1 <= i && i <= a.length;
//@ loop_invariant (\forall int j; 0 <= j && j < i; m >= a[j]);
//@ loop_invariant (\exists int j; 0 <= j && j < i; m == a[j]);
//@ decreases a.length - i;
```

They say that `m` is the maximum of the part already scanned and is an element
of that part. OpenJML can prove these and the existence postcondition, but it
still cannot prove that `m` is at least every element of the whole array.

My hypothesis was that the loop skips the last element. If that element is the
largest, the answer is wrong. This is a code error. I kept it for exercise 5,
then fixed the condition to `i < a.length`.

### 4. BinarySearch

Q: What does OpenJML report, in which method, and for which concrete call? How large must the array be?

In `midpoint`, `(lo + hi) / 2` causes an `ArithmeticOperationRange` failure for
the addition and a `Postcondition` failure for the result's range. `search` can
still verify using the contract of `midpoint`.

For example, `midpoint(1073741824, 1073741824)` satisfies the precondition, but
the sum wraps to -2147483648 and the result is -1073741824.

To reach this through valid array indices, the array needs at least 1073741825
elements, or `2^30 + 1`. The largest index must satisfy
`2 * (length - 1) > Integer.MAX_VALUE`.

For an array of that length filled with zeros, searching for 1 eventually reaches
`lo = hi = 1073741824`. The midpoint becomes negative and the array access fails.
I worked out this example from the bounds; I did not allocate the roughly 4 GiB array.

Q: What happens without `/*@ pure @*/` on `midpoint`, and why?

Removing `pure` adds an `Assignable` error involving `\everything` and
`LoopInvariant` failures for the array properties in `search`.

Without `pure` or another frame condition, the caller must allow for the method
changing any writable heap location. It can no longer assume the array stays
the same, and the call also conflicts with the loop's allowed modifications.

I restored `pure` and fixed the calculation to:

```java
return lo + (hi - lo) / 2;
```

Since `0 <= lo <= hi`, the subtraction is safe and the result is between `lo`
and `hi`.

## JBMC

### 5. Max, again

Q: What input did JBMC find, and what goes wrong? Was your hypothesis of exercise 3 right?

With `--unwind 3 --no-unwinding-assertions`, JBMC found `a = {3, 32770}`.
The original loop does not run for an array of length 2, so it returns 3.
The harness fails at `j = 1` when checking `r >= a[j]`. This confirms that the
loop skips the last element.

Q: Smallest `--unwind` and `--max-nondet-array-length` that find it? Relation to the small scope hypothesis?

Both minimum bounds were 2. This command found the counterexample
`{-1, 2147483647}`:

```sh
./bmc MaxCheck.check --unwind 2 --max-nondet-array-length 2 --no-unwinding-assertions
```

With unwind 1, the failing check for the second element is not reached. With an
array length limit of 1, returning the only element is always correct.

This fits the small scope hypothesis: a very small input can expose the bug.
Passing a small scope alone does not prove correctness for larger inputs.

Q: Why does `--unwind 5` with unwinding assertions fail on the fixed version? Smallest K with `--max-nondet-array-length 4`, and why not one less? What has been proved?

After fixing the loop, `--unwind 5` still fails because the default maximum array
length is 5. The harness needs to check all 5 elements and then check the loop
condition once more. The failure is an unwinding assertion, not a maximum-value
assertion.

With `--max-nondet-array-length 4`, the smallest successful K is 5:

```sh
./bmc MaxCheck.check --unwind 5 --max-nondet-array-length 4
```

K = 4 is still too small for the harness's exit check. With the default length
limit of 5, K = 6 is needed.

The successful run proves the checked properties and safety checks for every
non-empty array of length at most 4, with arbitrary int elements. It does not
prove the result for arrays of arbitrary length.

### 6. SumX

Q: Which values of `x` were checked with `--unwind 10 --no-unwinding-assertions`? Why does it fail with unwinding assertions? Which K is a proof? Sizes and times for K = 10, 100 and that K.

My harness assumes `0 <= x && x <= 1000`, calls `SumX.sum(x)`, and checks
`r == x * (x + 1) / 2`. The Java multiplication in this assertion is safe for
that input range.

With `--unwind 10 --no-unwinding-assertions`, only x = 0..9 reach the assertion
after the call. Inputs needing more iterations are cut off. I also checked
reachability: x = 9 can return, but x >= 10 cannot reach the position after the
call at this bound.

With unwinding assertions enabled, K = 10 fails because some allowed inputs
need more iterations. The smallest K for a full proof is 1001: up to 1000 loop
iterations plus the exit check. K = 1000 still fails for x = 1000, while K = 1001
passes for all x = 0..1000.

These measurements all use `--no-unwinding-assertions` for comparison:

| K | SAT variables | SAT clauses | Solver time (s) | Total time (s) | x reaching the assertion |
| --- | ---: | ---: | ---: | ---: | --- |
| 10 | 4635 | 13635 | 0.003497 | 0.995671 | 0..9 |
| 100 | 9584 | 30251 | 0.022867 | 0.607602 | 0..99 |
| 1001 | 66867 | 666127 | 1.810850 | 2.762294 | 0..1000 |

The full proof command, with unwinding assertions enabled, is:

```sh
./bmc SumXCheck.check --unwind 1001
```

It passed with 66870 variables, 666136 clauses, 1.462060 s solver time and
2.438174 s total time. Total time includes compilation and the script. These
are single-run timings on my machine, so they can vary. The formula clearly
gets larger as K increases.

Q: What did OpenJML need from you, and what did JBMC need?

OpenJML needed the contract, the invariant `s == i * (i + 1) / 2`, and
`decreases x - i`. It uses induction to prove the loop without unrolling every
iteration.

JBMC needed an assume/call/assert harness and an unwind bound. To cover the
whole allowed input range, I needed K = 1001 and passing unwinding assertions.

### 7. BinarySearch

Q: Why does JBMC miss the bug with the `search` harness? Could a larger bound help?

With the original midpoint, K = 6 and arrays of length at most 5, JBMC reports
SUCCESSFUL. The indices are at most 4, so `lo + hi` is at most 8 and cannot
overflow.

Increasing K alone does not increase the array size. Increasing
`--max-nondet-array-length` alone also does not help because the harness assumes
`a.length <= 5`. Even if both limits were changed, an array with over a billion
elements would make the sorting constraints and loop unrolling impractical.
Checking `midpoint` directly is much simpler.

Q: What did the `midpoint` harness find?

The harness assumes `0 <= lo && lo <= hi`, calls `midpoint`, and checks
`lo <= r && r <= hi`. It adds no extra restrictions on the integer inputs.

With the original code and `--unwind 1`, JBMC found:

```text
lo = 229638144
hi = 2068840448
r  = -998244352
```

The inputs satisfy the precondition, but their sum overflows and the result is
negative. After restoring the safe calculation, the same harness passes.
There are no loops or arrays in this check, so K = 1 covers all pairs of int
inputs satisfying the precondition.

## Comparison

### 8. Comparison

| Program | OpenJML: result and what I wrote | JBMC: result and bound |
| --- | --- | --- |
| SumX | Added the sum invariant and decreases clause. Proved correctness and termination for x = 0..1000. | Wrote the harness. K = 10 with truncation checks only x = 0..9; K = 1001 with unwinding assertions covers the full input range. |
| Max | Added invariants for the prefix maximum, its index range and a witness. Found the skipped last element; after the fix, the proof covers arbitrary allowed array lengths. | Found the bug with K = 2 and length limit 2. After the fix, K = 5 with unwinding assertions proves the properties for lengths up to 4. |
| BinarySearch | Found overflow in midpoint. With pure restored and the calculation fixed, both methods verify. | The search harness at K = 6 and length limit 5 misses the overflow. The direct midpoint harness finds it at K = 1 and passes after the fix. |

Q: When would you use each tool?

I would use OpenJML when I have a clear specification and need a proof for
arbitrary loop lengths. It needs suitable invariants, so a failed proof can mean
either a code bug or a missing piece of the specification.

I would use JBMC to find concrete counterexamples and check boundary or control
flow bugs without first writing invariants. Its result depends on the harness,
input limits and unwind bound. A full proof needs enough unrolling and passing
unwinding assertions.

Using JBMC to find a bug and OpenJML to prove the corrected code is a useful
combination.
