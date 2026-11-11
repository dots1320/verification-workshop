# Homework plus: answers

Name(s): Yin ZeYan (GitHub: dots1320)

工具：OpenJML 21.0.29、JBMC 6.11.0。以下结果来自实际运行；临时加入的错误已撤回。

### 1. Invariants from an LLM

| method | LLM | rounds | mistakes | final invariants by |
| --- | --- | --- | --- | --- |
| count | Codex（本次对话） | 1 | 首轮通过，无工具报告的错误 | Codex 编写，OpenJML 验证 |
| reverse | Codex（本次对话） | 1 | 首轮通过，无工具报告的错误 | Codex 编写，OpenJML 验证 |
| isqrt | Codex（本次对话） | 1 | 首轮通过，无工具报告的错误 | Codex 编写，OpenJML 验证 |
| dutchFlag | Codex（本次对话） | 1 | 首轮通过，无工具报告的错误 | Codex 编写，OpenJML 验证 |

- `count`：`c` 等于已扫描前缀中的匹配数，并有 `0 <= c <= i`。
- `reverse`：两端已经反转，中间保持原值，左右下标对称。
- `isqrt`：保存 `r*r <= n`，并用 `0 <= r <= 1000` 保证运算安全。
- `dutchFlag`：保存下标顺序，以及已经分好的 0、1、2 三段。

四个方法分别检查和全文件检查均通过。实际没有失败轮次，未人为编造重试记录。

Q: Why is it safe to use invariants written by an LLM here, even if the LLM is often wrong?

LLM 只提出候选，OpenJML 检查初始化、每轮保持、退出后的结论、安全性和递减量。
候选是否可用由验证工具裁定，不能仅相信 LLM 的描述。证明仍依赖契约准确表达需求，
以及工具的可信假设；弱契约本身不能证明没有写出的要求。

### 2. The Zune bug

Q: `--unwind 31 --no-unwinding-assertions` says SUCCESSFUL. Does that mean `yearOf` is correct for every day it checked?

不能这样推断。它只检查边界内到达断言的执行，过长或不终止的执行被截断。
即使所有返回的年份都在范围内，也不代表每个允许输入都能返回，或年份一定准确。

Q: What does JBMC report without `--no-unwinding-assertions`? Is K too small, or is something else wrong?

开启 unwinding assertions 后失败。K=31 的一个输入为 days=1827，最后停在
year=1984、days=366，循环不再改变状态。把 K 增到 60 仍失败，另一个反例
是 days=366，直接在 1980 年停滞。这是死循环，不是计算有限但边界稍小。

Q: What is wrong with the loop? Which date froze the Zune?

外层要求 `days > 365`，但闰年分支只有 `days > 366` 才更新。
剩余恰好 366 天时会一直重复。冻结日期是 **2008 年 12 月 31 日**，
即从 1980-01-01 起第 10593 天；处理到 2008 年时恰好剩下 366 天。

修复采用直接的流程：算出当前年有 365 还是 366 天；剩余天数属于本年则退出，
否则扣掉该年的天数并增加年份。

Q: With your fix, what is the smallest K that gives VERIFICATION SUCCESSFUL with unwinding assertions? What exactly has been proved?

最终实现实测最小 **K=30**：K=29 仍有 unwinding assertion 失败，K=30 成功。
最多要扣除 29 个完整年份，再完成退出检查。两个 harness 在 K=30 都通过。

结论覆盖原前置条件的 **days=1..10950**：方法能终止，年份在范围内，
而强 harness 进一步证明日期落在返回年份中。`MAX_DAYS=365*30` 没有计入闰日，
实际覆盖到 2009-12-23，不能声称覆盖完整的 30 个公历年或任意整数输入。

Q: A colleague changes `days > 366` to `days >= 366`. Which harness notices, and why?

在原始版本上做该修改，弱 `yearOfInRange` 仍通过；强 `yearOfIsRight` 失败。
反例 days=366 本应属于 1980 年最后一天，却扣到 days=0，错误返回 1981。
1981 仍在允许的年份范围内，所以弱属性发现不了。

强 harness 用 `before=daysBefore(year)` 检查
`before < days && days <= before + 本年天数`，能够识别这个跨年错误。
最终已撤回伪修复，保留正确实现。

Q (★): Why does `./esc` say OK on the original? What changes with `decreases`?

原始证明是部分正确性：如果方法返回，结果满足给定范围契约；没有证明一定返回。
加 `decreases days` 后，OpenJML 在原始版本报告 `LoopDecreases`，因为闰年的
第 366 天没有任何进展。最终正确实现保留该递减量，并通过验证。

### 3. Range

Q: Why does `size()` not verify? Give concrete values.

`lo <= hi` 不保证区间长度能放进 int，且 `hi-lo` 和后续 `+1` 都可能溢出。
OpenJML 报 `ArithmeticOperationRange` 和 `Postcondition`。
例如 lo=-2147483648、hi=2147483647，正确长度为 **4294967296**，int 无法表示。

Q: Compare JBMC's counterexample with your answer above.

JBMC 实际给出 lo=-633754814、hi=1972821695；正确长度为 2606576510，
原实现却返回 -1688390786。与上述分析一样，都是整数溢出。

最终保留原 `ensures`，把返回类型改为 `long`，实现为
`return (long) hi - lo + 1;`。转换发生在减法之前，整个计算都使用 long。
OpenJML 和 `RangeCheck.size --unwind 1` 均通过，没有限制原输入范围。

### 4. StackAr

Q: Which tool reports your bug, and how? Could a bug get past OpenJML but not JBMC, or the other way around?

栈只用数组和 top 实现；空栈 top=-1，满栈 top=容量-1。
类不变量约束 top 的范围，方法契约描述结果和 top 的变化，`assignable` 限制修改位置。
容量 0 合法，此时同时为空和满。最终 OpenJML 与给定的 K=5 JBMC 检查均通过。

临时删除 `pop` 中的 `top--` 后，两工具都发现问题：

- OpenJML 报 `pop` 的 `Postcondition`，无法保证 top 减少 1。
- JBMC 在 `s.size() == n` 断言失败：容量 1 的栈 push 后 pop，模型数量减少，真实栈未减少。

若契约过弱、漏掉某项行为，OpenJML 可能通过，而模型对比的 JBMC 仍能发现错误。
反过来，JBMC 的小边界可能漏掉较长序列或较大容量的错误，OpenJML 却能发现违反规范。
两者都必须结合各自的规范与覆盖范围解释。临时错误已撤回。

### 5. SafeLock

Q: Smallest K that finds a bug? Which sequence of events? What is wrong in the code?

原始版本实测 K=1..4 成功，最小找错边界为 **K=5**，事件为：

```text
错 PIN → 错 PIN → Close → 错 PIN → 正确 PIN
```

原实现即使仍为 LOCKED，Close 也清零内部 failed。于是共发生三次错误且没有正确
PIN 或管理员复位，内部却只记一次，之后正确 PIN 仍能开门，违反 harness 属性。
最简单修复是把 `failed=0` 移到 `state==OPEN` 的分支内；锁定或阻塞时的 Close 不清零。

Q: Formula size and time for K = 8, 10, 12.

以下是修复后原 Property 1、带 `--no-unwinding-assertions` 的一次实测：

| K | SAT variables | SAT clauses | 求解时间 / s | 总耗时 / s | 结果 |
| --- | ---: | ---: | ---: | ---: | --- |
| 8 | 46050 | 68865 | 0.181350 | 0.809728 | SUCCESSFUL |
| 10 | 56941 | 87971 | 0.354194 | 1.042682 | SUCCESSFUL |
| 12 | 67836 | 107563 | 0.669870 | 1.342203 | SUCCESSFUL |

求解时间来自 JBMC，包含编译和脚本的总耗时单独列出；时间受本机负载影响。
新写的 `onlyAdminUnblocks` 在 K=8、12 也通过：若从 BLOCKED 离开，事件必须是
管理员复位且 code 正确。它没有额外限制 pin 与 adminCode 的取值。

Q: Does SUCCESSFUL with K = 12 mean the property holds for every sequence? Can unwinding assertions help?

只排除了给定展开范围内的反例，不能推出任意长事件序列都成立。
事件循环由 nondetBoolean 控制，可任意长，任何有限 K 都无法证明它已经穷尽。
实测开启 unwinding assertions 后失败于 harness 的循环展开断言，增加有限 K
也无法消除这个问题。bonus 用归纳不变量证明状态性质，不依赖固定的事件次数。

### Final checks

最终验证通过的 OpenJML 文件为 `LlmLoops`、`Zune`、`Range`、`StackAr`、`SafeLock`。
最终 JBMC 检查均成功：两个 Zune harness（K=30，开启 unwinding assertions），
Range（K=1）、StackAr（K=5，截断），以及两个 SafeLock harness（K=8，截断）。
所有占位 `assert false` 已删除，实验中的错误均已撤回。
