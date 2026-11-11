# Homework: answers

Name(s): Yin ZeYan (GitHub: dots1320)

实验环境：OpenJML 21.0.29、JBMC 6.11.0、Java 21.0.4。
以下“原始版本”指仓库最初给出的代码；最终提交的源码保留修复。

## OpenJML

### 1. Absolute

Q: What does OpenJML complain about before you write a contract, and for which input?

原始版本在 `return -n;` 报 `ArithmeticOperationRange: int negation`。
触发输入是 `n = Integer.MIN_VALUE = -2147483648`。
它的数学绝对值是 `2147483648`，超出了 `int` 的最大值
`2147483647`；Java 的取反运算会回绕，结果仍为 `-2147483648`。

Q: Which `requires` did you need, and why? Could you avoid it by changing the `ensures`?

使用 `requires n > Integer.MIN_VALUE;`，排除唯一无法用非负 `int`
表示其绝对值的输入。两个后置条件分别要求结果非负，以及结果为 `n` 或 `-n`。

若保持题目要求的“结果非负”，就必须排除这个输入，或改变返回类型及实现。
把后置条件放宽为允许最小整数返回自身，只是在描述 Java 的回绕行为，
已经不满足原来的绝对值要求。并且本项目默认使用安全算术检查：实测仅放宽
`ensures`、删除 `requires`，取反的 `ArithmeticOperationRange` 仍然存在。
所以仅修改 `ensures` 不能解决本题的溢出义务。

### 2. SumX

Q: Which proof obligations fail? Is the program wrong?

原始版本只有 `0 <= i && i <= x` 这一不变量，报告两类未证明的义务：

- 返回处的 `Postcondition`：无法证明 `s == x * (x + 1) / 2`。
- `s = s + i` 的 `ArithmeticOperationRange`：无法排除加法溢出。

在给定的 `0 <= x <= 1000` 内，程序本身计算正确。问题在于原不变量
没有说明 `s` 与 `i` 的关系；验证器抽象循环时不能据此确定累加值的范围。
加强为下面的不变量后，验证通过：

```java
//@ loop_invariant 0 <= i && i <= x && s == i * (i + 1) / 2;
```

它在初始化时成立；一轮中先增加 `i`，再把新的 `i` 加入 `s`，该关系仍成立。
退出时由 `i <= x` 和 `!(i < x)` 得到 `i == x`，因而推出后置条件。
`decreases x - i` 则提供终止证明所需的递减量。

Q: Largest N for which `x <= N` verifies? What happens with N + 1, and why?

实测最大上界为 **N = 65535**：

```text
65535 * 65536 / 2 = 2147450880 <= Integer.MAX_VALUE
65536 * 65537 / 2 = 2147516416 >  Integer.MAX_VALUE
```

`x <= 65535` 时 OpenJML 验证成功。改为 `x <= 65536` 后，报告
`s = s + i` 的 `ArithmeticOperationRange`，以及累加值不变量的
`LoopInvariant` 失败：最后一次累加可能溢出，Java 结果回绕为负数，
无法继续满足精确求和关系。

JML 中本题的规范表达式按数学整数计算，所以规范里的中间乘法不会把上界
限制成 46340。最终已经把前置条件保留为 **`x <= 1000`**，供第 6 题使用。

### 3. Max

Q: Is the remaining failure caused by your invariants or by the code? (Your hypothesis.)

在原始循环条件 `i < a.length - 1` 下补充：

```java
//@ loop_invariant 1 <= i && i <= a.length;
//@ loop_invariant (\forall int j; 0 <= j && j < i; m >= a[j]);
//@ loop_invariant (\exists int j; 0 <= j && j < i; m == a[j]);
//@ decreases a.length - i;
```

这说明 `m` 是已扫描前缀 `a[0..i)` 的最大值，而且确实来自这个前缀。
此时不变量本身和存在性后置条件能够证明，剩余失败是返回值不小于
**整个数组**所有元素的 `Postcondition`。

第 3 题阶段的假设是代码有边界错误：循环跳过了最后一个元素。
如果最后一项比前面的元素都大，返回值就不是真正的最大值。
这是代码问题，不能靠加强真实的不变量消除。先保留该错误用于第 5 题实验；
第 5 题确认后，最终把循环条件修复为 `i < a.length`。

### 4. BinarySearch

Q: What does OpenJML report, in which method, and for which concrete call? How large must the array be?

原始 `midpoint` 的 `(lo + hi) / 2` 报 `ArithmeticOperationRange`
（`lo + hi` 可能溢出）和 `Postcondition`（结果可能不在 `[lo, hi]` 内）。
原始 `search` 自身仍可根据 `midpoint` 的契约完成模块化验证。

例如 `midpoint(1073741824, 1073741824)` 满足前置条件，
但加法回绕为 `-2147483648`，除以 2 后得到 `-1073741824`，违反结果范围。

要在实际二分搜索中通过合法数组下标触发它，数组长度至少需要
**1073741825，即 `2^30 + 1`**。因为最大下标为 `length - 1`，必须有
`2 * (length - 1) > Integer.MAX_VALUE` 才可能发生下标之和溢出。

一个具体的可达场景是搜索长度为 1073741825、元素全为 0 的有序数组，
目标为 1：搜索不断向右，最终到达 `lo = hi = 1073741824`，
错误中点变成负数，随后数组访问越界。该巨型数组示例是根据边界推导的，
实验没有实际分配约 4 GiB 的数组。

Q: What happens without `/*@ pure @*/` on `midpoint`, and why?

临时删除 `pure` 后，除了原有的中点错误，还出现调用处的 `Assignable`
错误（涉及 `\everything`），以及 `search` 中左右两侧元素性质的
`LoopInvariant` 失败。

调用者使用被调用方法的契约推理。`pure` 提供不修改调用者可见堆状态的保证；
删除它且没有给出其他 frame condition 时，方法默认可能修改所有可修改的堆位置。
验证器因此不能假定数组内容在调用后保持不变，数组上的循环不变量也就无法保持；
该调用的允许修改范围还与循环的修改范围冲突。

最终恢复 `pure`，保留原始实现的注释，并修复为：

```java
return lo + (hi - lo) / 2;
```

由 `0 <= lo <= hi`，减法不溢出，最终结果也不超过 `hi`，因此整个计算安全。

## JBMC

### 5. Max, again

Q: What input did JBMC find, and what goes wrong? Was your hypothesis of exercise 3 right?

对仍保留原始 bug 的版本运行：

```sh
./bmc MaxCheck.check --unwind 3 --no-unwinding-assertions
```

本次反例是 `a = {3, 32770}`。原始循环对长度 2 的数组一次也不执行，
返回首项 3；harness 在 `j = 1` 检查 `r >= a[j]` 时失败。
这确认了第 3 题“循环漏查最后一项”的假设。

Q: Smallest `--unwind` and `--max-nondet-array-length` that find it? Relation to the small scope hypothesis?

保留 `--no-unwinding-assertions`，实测两个最小边界都为 **2**，可以同时使用：

```sh
./bmc MaxCheck.check --unwind 2 --max-nondet-array-length 2 --no-unwinding-assertions
```

该次反例是 `{-1, 2147483647}`。`--unwind 1` 无法观察到对第二项的失败检查；
把数组长度上限限制为 1 时，返回唯一元素始终正确，因此不能暴露这个错误。

只需两个元素就能暴露缺陷，符合 small scope hypothesis 的直觉：很多错误有很小的
反例。不过小范围内检查成功，不能据此证明所有更大输入都正确。

Q: Why does `--unwind 5` with unwinding assertions fail on the fixed version? Smallest K with `--max-nondet-array-length 4`, and why not one less? What has been proved?

修复为 `i < a.length` 后，默认输入数组上限仍为 5。
`--unwind 5` 的失败来自 `MaxCheck` 遍历数组的 **unwinding assertion**，
而不是最大值断言：展开次数不足以完成长度 5 的 harness 循环及其退出检查。

指定 `--max-nondet-array-length 4` 后，最小完整验证边界为 **K = 5**：

```sh
./bmc MaxCheck.check --unwind 5 --max-nondet-array-length 4
```

K = 4 仍在 harness 的 unwinding assertion 失败；最多需要检查 4 个元素，
并完成退出时的条件检查。保持默认数组上限 5 时，K = 6 才能全部通过。

K = 5、数组上限 4 的成功证明：对于所有非空、长度至多 4、元素可为任意 `int`
的数组，给定最大值性质和工具的安全性检查均成立，且展开已经充分。
这个 JBMC 结论不涵盖任意长度数组；OpenJML 的不变量证明不依赖这个长度上限。

### 6. SumX

Q: Which values of `x` were checked with `--unwind 10 --no-unwinding-assertions`? Why does it fail with unwinding assertions? Which K is a proof? Sizes and times for K = 10, 100 and that K.

补写的 harness 忠实采用原契约：假设 `0 <= x && x <= 1000`，调用 `SumX.sum(x)`，
断言 `r == x * (x + 1) / 2`。该输入范围内后置断言的 Java 中间乘法也不会溢出。

`--unwind 10 --no-unwinding-assertions` 虽然显示 SUCCESSFUL，
真正到达求和后置断言的只有 **x = 0..9**。需要更长循环的输入在边界被截断，
没有完成后置条件检查。临时的覆盖实验也确认了 x = 9 可以返回，x >= 10 的返回后
位置不可达；覆盖实验文件不属于提交源码。

去掉 `--no-unwinding-assertions` 后，K = 10 报循环的 unwinding assertion 失败，
表明允许的某些输入需要更多展开，并不意味着求和程序算错。
最小完整证明边界是 **K = 1001**：最多执行 1000 次循环体，还要完成退出检查。
实测 K = 1000 在 x = 1000 时仍失败，K = 1001 则全部通过，覆盖 x = 0..1000。

以下三行统一使用 `--no-unwinding-assertions`，以相同口径比较规模：

| K | SAT variables | SAT clauses | 求解时间 / s | 总耗时 / s | 到达后置断言的 x |
| --- | ---: | ---: | ---: | ---: | --- |
| 10 | 4635 | 13635 | 0.003497 | 0.995671 | 0..9 |
| 100 | 9584 | 30251 | 0.022867 | 0.607602 | 0..99 |
| 1001 | 66867 | 666127 | 1.810850 | 2.762294 | 0..1000 |

开启 unwinding assertions 的完整证明命令是：

```sh
./bmc SumXCheck.check --unwind 1001
```

这次实验为 66870 variables、666136 clauses，求解时间 1.462060 s，
总耗时 2.438174 s，VERIFICATION SUCCESSFUL。
求解时间来自 JBMC 的 decision procedure 输出，总耗时还包含脚本、编译等开销。
以上是本机一次测量，受到缓存及并行实验影响，时间不应视为稳定基准；公式规模随 K
增大明显增加。

Q: What did OpenJML need from you, and what did JBMC need?

OpenJML 需要前后置条件，以及连接循环中间状态与最终结果的归纳不变量
`s == i * (i + 1) / 2`，并用 `decreases x - i` 证明终止。
它据此对所有满足前置条件的输入进行证明，无需按次数展开完整循环。

JBMC 需要把契约转换为 `assume / call / assert` harness，并提供展开边界。
小 K 加截断只检查部分执行；若要覆盖本题全部允许输入，需要开启并通过
unwinding assertions，这里最小为 K = 1001。

### 7. BinarySearch

Q: Why does JBMC miss the bug with the `search` harness? Could a larger bound help?

恢复原始中点实现后，`search` harness 在 K = 6、数组上限 5 下仍显示 SUCCESSFUL。
数组下标至多为 4，`lo + hi` 至多为 8，无法触发整数溢出。
因此这是给定小数组范围内的正确性结论，不能推翻 OpenJML 对大整数情况的发现。

仅增大 `--unwind` 不会扩大输入数组。仅增大 `--max-nondet-array-length` 也不够，
因为这个 harness 还显式假设 `a.length <= 5`。即便同时扩大 harness 允许范围，
要到十亿级数组长度才能触及该错误，排序约束及遍历的展开规模在实践中不可行。
直接检查只接收两个整数的 `midpoint` 更合适。

Q: What did the `midpoint` harness find?

新 harness 假设 `0 <= lo && lo <= hi`，直接调用 `midpoint`，
断言 `lo <= r && r <= hi`，不增加任何限制整数范围的假设。

原始版本用 `--unwind 1` 找到的实际反例是：

```text
lo = 229638144
hi = 2068840448
r  = -998244352
```

输入满足前置条件，但 `lo + hi` 溢出，返回负数，违反范围后置条件。
恢复安全中点实现后，同一 harness 显示 VERIFICATION SUCCESSFUL。
该 harness 及调用没有循环，也无需分配数组，所以 K = 1 不限制两个合法 `int`
参数的取值；修复后的结论涵盖所有满足该前置条件的整数参数组合。

## Comparison

### 8. Comparison

| program | OpenJML: result, what you wrote | JBMC: result, bound used |
| --- | --- | --- |
| SumX | 原不变量过弱；加入累加值与进度的关系后，证明 x = 0..1000 全部正确，并证明终止。 | 编写求和 harness；K = 10 加截断只覆盖 x = 0..9，K = 1001 且开启 unwinding assertions 完整覆盖给定前置条件。 |
| Max | 补充前缀最大值、范围和见证不变量；发现遗漏末元素，修复后证明所有满足前置条件的数组，不依赖小数组上限。 | 原始 bug 在 K = 2、数组上限 2 时已有反例；修复后 K = 5、数组上限 4 且开启 unwinding assertions 成功，结论限于该长度范围。 |
| BinarySearch | 用原契约和不变量发现 midpoint 溢出；保留 pure 并修复算式后，midpoint 与 search 验证通过。 | search 的 K = 6、数组上限 5 检查漏掉大下标溢出；编写直接 midpoint harness 后 K = 1 找到反例，修复后同一检查通过。 |

Q: When would you use each tool?

需要证明不受小规模输入限制的循环性质、已有清晰数学规范且能够写出不变量时，
适合用 OpenJML。它的证明能力强，但验证失败可能来自程序错误，也可能来自缺少
足够的规范或不变量，需要区分。

需要快速寻找具体反例、检查边界和控制流错误，或暂时不容易写不变量时，
适合用 JBMC。必须说明 harness 的输入范围、K 以及是否启用 unwinding assertions；
小范围 SUCCESSFUL 只代表那个范围没有发现反例。对于能完整覆盖的有限输入域，
充分展开并通过 unwinding assertions 也能形成完整证明。

实践中可先用 JBMC 反例定位错误，再修复代码并用 OpenJML 证明更一般的性质。

## Final checks

以下检查在最终修复版本上均通过；没有削弱给定的契约或已有 harness。

```sh
./esc hw/Absolute.java
./esc hw/SumX.java
./esc hw/Max.java
./esc hw/BinarySearch.java
./bmc MaxCheck.check --unwind 5 --max-nondet-array-length 4
./bmc SumXCheck.check --unwind 1001
./bmc BinarySearchCheck.midpoint --unwind 1
./bmc BinarySearchCheck.search --unwind 6 --max-nondet-array-length 5
```

最终 `SumX` 上限为 1000，`midpoint` 已恢复安全实现及 `pure`，两个待补 harness
中的 `assert false` 占位均已删除。
