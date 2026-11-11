# Bonus: answers

Name(s): Yin ZeYan (GitHub: dots1320)

工具：OpenJML 21.0.29、JBMC 6.11.0。以下原始 bug 实验先保留单节点前置条件；
最终代码还完成了安全添加子树的可选扩展。

### 1. Composite

Q: Which part of the invariant breaks, after which calls? What is wrong in `update`?

补齐检查：value 必须是 initValue 与直属子节点值的最大值；maxChild 为空当且仅当
value 等于 initValue，否则必须指向一个直属子节点，且该子节点的值等于 value。
原来的父指针反向一致性检查也保留。

两次添加即可触发错误。例如令 A、B、C 初值分别为 0、1、2：
先 `A.addChild(B)`，再 `B.addChild(C)`。第二次更新传播到 A 时，
原来的 `parent.update(c)` 把 C 传给 A，导致 A.maxChild 指向孙节点 C，
违反“maxChild 是直属子节点”的要求。实际 K=4 反例也是这样的祖孙结构，
失败断言为 `hasMaxChild`。

修复只需改成 `parent.update(this)`：每一层都把自身作为上一层的直属子节点传递。
原始代码 K=4、5 均失败，修复后两个边界均通过。

Q: Why does JBMC need K = 4 to find a bug that needs two calls?

`--unwind` 约束所有循环，不只是添加次数。初始化需要创建 3 个节点，
还要完成该循环的退出检查，因此至少需要 K=4。
实测 K=2、3 虽然 SUCCESSFUL，但初始化就被截断，没有产生 SAT 公式，
根本没有到达后面的不变量检查；不能把它们当成树结构正确的证据。

Q: How large is the formula? What would you need to verify `Composite` with OpenJML?

先保持原单节点前置条件，使用完整局部不变量比较原始 bug 版本：

| K | SAT variables | SAT clauses | 求解时间 / s | 结果 |
| --- | ---: | ---: | ---: | --- |
| 2 | 未产生公式 | 未产生公式 | — | 初始化被截断 |
| 3 | 未产生公式 | 未产生公式 | — | 初始化被截断 |
| 4 | 136022 | 334704 | 3.370900 | FAILED |
| 5 | 193043 | 498099 | 4.260529 | FAILED |

相较 hw 的 Max（约 7646 个变量），这个堆模型大得多：必须编码对象、引用、
别名、父子关系及不同调用历史。相较其他题，变量数和子句数不一定都更大，
例如 hw 的 SumX K=1001 有约 666136 个子句；复杂度取决于模型和展开界。

要用 OpenJML 证明一般大小的树，需要描述可达节点、无环性、父子关系和缓存最大值，
还要写清允许修改哪些节点的 frame condition、递归 update 的契约及终止依据。
更新一个节点会影响祖先，如何保持相关对象的不变量也是证明的一部分。
三个节点的有界检查不能替代这个一般性证明。

Q (★): What goes wrong when subtrees are allowed?

只删除 `c.firstChild == null` 会允许把祖先重新接到后代下面，形成环。
例如先 `B.addChild(C)`，再 `C.addChild(B)`。若缓存值没有变化，
父指针与局部最大值检查仍可能全部成立；实测局部检查 K=5 仍 SUCCESSFUL。
加入父链无环检查后，同样的扩展在 K=5 找到了环。

最终代码安全支持子树：

- `addChild` 仍要求 c 是另一棵树的根，并沿 this 的祖先链拒绝 c，防止形成环。
- harness 对应只发起合法的无环添加；原来允许的单节点添加没有被排除。
- checker 最多移动 NODES 次父指针，并显式断言最后到达 null。
  三节点模型中，环会违反这个断言，不是仅依赖展开截断来忽略它。

最终扩展版本的实际结果：

| K | SAT variables | SAT clauses | 求解时间 / s | 结果 |
| --- | ---: | ---: | ---: | --- |
| 4 | 176330 | 444730 | 4.901620 | SUCCESSFUL |
| 5 | 253109 | 668824 | 5.406480 | SUCCESSFUL |

另用确定性测试在开启 unwinding assertions 时检查了“整棵子树可接入”和
“成环请求抛出 IllegalArgumentException”，两项都通过。
最终仍是三个节点及给定展开范围的验证，不是任意大小堆的证明。

### 2. SafeLock for any number of events

Q: Why does OpenJML think `failed++` may overflow?

OpenJML 逐方法验证。只有构造时 failed=0，不能说明任意一次方法入口的 failed 范围。
缺少类不变量时，工具无法排除 failed 已接近 int 上限，因而报告 ArithmeticOperationRange。

最终采用三条直接的不变量：

```java
//@ private invariant 0 <= failed && failed <= MAX_ATTEMPTS;
//@ private invariant (state == State.BLOCKED) <==> (failed == MAX_ATTEMPTS);
//@ private invariant state == State.OPEN ==> failed == 0;
```

只有 LOCKED 状态会执行自增。由不变量，此时 failed 不可能等于 3，
因此最多为 2，自增是安全的；各状态转移也保持这些关系。
修复后的 `./esc plus/SafeLock.java` 验证通过。

Q: Does your invariant catch the bug of homework plus, exercise 5? What does this proof give you that JBMC did not?

能。临时恢复原 close 错误后，OpenJML 在 close 出口报告 InvariantExit：
BLOCKED 状态下 Close 把 failed 从 3 清为 0，破坏状态与计数的一致性。
最终已经恢复修复。

归纳证明不受事件次数 K 限制：初始成立，每次合法调用都保持成立，
因而任意有限调用历史都保持这些状态关系及相应算术安全性。
JBMC 的有限事件展开不能直接给出这一无界结论。

同时，这三条状态不变量没有记录完整的历史错误 PIN 次数；不能仅凭它们声称
完整证明了两个 harness 的所有历史性质。若要无界证明那些性质，还需相应的
方法转移契约或历史/ghost 状态。

### Final checks

- `./bmc CompositeCheck.addChildren --unwind 5 --no-unwinding-assertions` 成功。
- `./esc plus/SafeLock.java` 成功。
- `Composite` 保留正确的逐层缓存更新与子树防环检查，`SafeLock` 保留正确的 Close 行为。
