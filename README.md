# 最大度四图的候选边诱导匹配：从 19.5 到 19

本仓库保存新的研究推导与验证记录。当前目标是判断并尝试证明

\[
|F|\le 19\nu_s^G(F)+t_G(F).
\]

**截至 2026-10-11：19 倍猜想尚未证明，也没有找到反例。**

强冲突始终在完整原图 `G` 中判断。`F` 外的原边仍可作冲突见证。
`t_G(F)` 只计数全部二十条边均被选取的原图 `C₅[2]` 连通分量。

## 阅读入口

- [路线 B 第一阶段：严格推导、前提修正与临界配置](notes/route-b-stage1.md)
- [验证范围及复现方法](verification/README.md)
- [本轮实际验证结果](verification/results.json)
- [验证脚本](scripts/verify-upstream.ps1)

## 已有证明与新研究的边界

已有修正 19.5 定理、五项高冲突度团界、二十团刚性及分量计数来自
[strong-edge-packing-195](https://github.com/congyuemao/strong-edge-packing-195)。
该工程通过 Git 子模块固定在提交
`2e91b05b25a4ee931a0490fefcdbb4f253be95c8`：

- [英文证明手稿](upstream/packing195/manuscript/packing195.md)
- [Lean 主定理](upstream/packing195/lean/StrongEdge/TightComponents.lean)
- [已有局部 39 界](upstream/packing195/lean/StrongEdge/MinimalPacking195.lean)

本轮补偿恒等式、三级最优选取下的零亏损中心性质、39 边临界配置归约，
均在本仓库中作为**纸面证明、尚未形式化**的结论记录。
上游 Lean 验证日志不为这些新结论提供形式化认证。

本阶段没有进行 SAT、CP-SAT 或完整图枚举，也没有排除任何一行 39 边临界配置。

## 取得固定的上游源码

在本仓库中执行：

```sh
git submodule update --init --recursive
```

不要执行子模块的 `update --remote` 来替换本次核对的固定版本。
新研究不修改上游已验证的数学源码、工具链或依赖锁文件。

## 后续工作

优先分析两个互不冲突的原边所覆盖的完整冲突闭邻域，及由此形成的两个临界私有团。
具体条件及仍待证明的命题见第一阶段记录的第 8 节。
即使完成 `k=2`，仍须处理 `k≥3`。
