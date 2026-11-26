# 棋王图上的完美匹配计数 · Lean 4

[English README](README.md)

英文短文 [Perfect matchings with two axial edges on the king’s grid](paper/main.pdf) 附有[可编译的 LaTeX 源码](paper/main.tex)。图和参考文献都在源码内，可用 Tectonic 编译，或用 pdfLaTeX 连续编译两次。

把棋盘上的每个格子和横、竖或对角相邻的一个格子配成一对，每格使用一次。棋盘边界不首尾相接，两条对角边可以交叉。在 $4\times4$ 的棋盘上，恰好含两条水平或竖直边的铺法有 12 种。在 $8\times8$ 的棋盘上有 80 种。

设 $A_j(m,n)$ 是 $2m\times 2n$ 棋盘上恰有 $j$ 条轴向边的铺法数。“轴向”指水平和竖直两种方向合计。项目形式化证明了

$$
A_0(m,n)=1,\qquad A_2(m,n)=n\binom{m+1}{2}+m\binom{n+1}{2}.
$$

取 $m=n$ 即得 $A_2(n,n)=n^2(n+1)$。Ryłko 将两个方盘公式列为猜想。查新发现，全对角铺法的唯一性已经包含在早期文献中，单个条带的二项式系数也有明确出处。现有项目的重点是完整棋盘与条带编码之间的对应，以及无遗漏、无重复的机器检验。[OEIS 原条目](https://oeis.org/A401673) · [查新记录与数学对应](docs/related-work.md)

## 复现

在安装了 Lean 4.19.0 和 Python 3.8 或以上版本的环境里，进入仓库根目录运行以下命令。使用 elan 时，仓库内的 `lean-toolchain` 会自动选择版本。无需安装 mathlib 或额外的 Python 包。[Lean 官方安装说明](https://lean-lang.org/install/)

```sh
lake build
python scripts/verify.py
python scripts/check_small_boards.py
```

`verify.py` 将源码复制到空的临时目录，重新编译并打印每条受审计定理的公理依赖。通过时最后一行是 `PASS: 11 modules, 29 axiom reports.`。可用 `--lean 路径` 指定 Lean 可执行文件，用 `--report audit.txt` 保存日志。独立的 Python 枚举器每次取第一个尚未覆盖的格子，逐一尝试它的合法伙伴，检查半边长从 0 到 4 的全部 25 个矩形。系统若以 `python3` 提供 Python，请使用该命令。[本次复验日志](docs/verification.txt)

## 怎样从整盘数到公式

偶数行与奇数行有同样多的格子。每一条非水平边在两者中各占一格，因此水平边必须在两类行里各占一半。按列考虑，竖直边也成偶数条，所以恰有两条轴向边时，它们必定平行。

设这两条边都水平。第一列每个格子的伙伴都在第二列，而且恰好占满第二列。依次剥去前两列，便得到 $n$ 个独立双列条带。看任意条带的顶行，两个格子要么水平配对，占一行；要么各自与下一行的对角格子配对，形成一个占两行的叉。因此每条带中水平边数为偶数，两条水平边必在同一条带。选中它有 $n$ 种办法。在这个条带里，把两个单行和 $m-1$ 个叉排成一列，两个单行的位置有 $\binom{m+1}{2}$ 种。转置棋盘即可得到竖直情形。全由对角边组成时，各条带都只能从上到下排满叉。

**从哪里读代码**：`DimerDiagonal.exactly_one_diagonal_tiling` 用配偶函数表达全对角匹配，证明它存在且唯一。`KingEnumeration.exactly_two_rectangle` 和 `KingEnumeration.exactly_two_square` 用无向边关系表达恰含两条轴向边的整盘匹配。证明从每个合法匹配恢复编码，再还原出相同的无向边集；交换一条边的两端或重新排列边，都不会重复计数。[全对角定理](KingGrid/Diagonal.lean) · [整盘计数定理](KingGrid/KingEnumeration.lean) · [编码还原](KingGrid/BoardRoundtrip.lean)

Codex 参与了选题检索、证明推导、Lean 实现与文档起草。验证软件及其说明使用 [MIT 许可证](LICENSE)。`paper/` 内的论文本身单独授权。
