[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22719535.svg)](https://doi.org/10.5281/zenodo.22719535)

# 偏元数学 · Day23 · 残差累积的平方根标度及其约束（S2 延续）· Lean 4 形式化验证

## Prenary Mathematics · Day23 · Square-Root Scaling of Residual Accumulation and Its Constraint (S2 Continuation) · Lean 4 Formal Verification

本文工作尚未得到独立实验验证，全部结论均为形式化验证层面的初步结果。

> **DOI**：待回填。本仓库为偏元数学新线 S2（第二程）的延续，上承 Day22 `prenary-math-lean-s2-action-foundation`（10.5281/zenodo.22719535）。

## 摘要

本仓库在偏元数学 004 地基（对象层 = ℂ；不定义方向偏好；ε ∈ (0, δ₀)）上，对"**残差累积的平方根标度**"及其**约束的来源**给出形式化见证，并补上"累积与复合"这一层的退化链与饱和闭式解。

六份文件、两条主线：
1. **标度**（Day23-01/02）——平方根标度的根据是正交（勾股）；独立 ⟹ 方差 ∝ n ⟹ √n 量级；完全相关 ⟹ ∝ n² ⟹ n 量级，两者不同阶；
2. **约束不外接**（Day23-03）——004 的最小模型配**线性复合**会与"上界不可达"冲突，**故 004 自身要求复合不能线性累加**——"不撞 δ₀"是 004 的自洽性要求，不是外接假设。

再加两份**结构件**：**Day23-04**（退化链闭合：δ₀ = 0 时残差集空、复合约束空真、标度压缩归零）；**Day23-06**（饱和闭式解 `R²(n) = D(1 − e^{−n/N})` 的起点、上界不可达、单调、早期线性上界）。

**关于第 5 份**：**Day23-05 是一份"重述"**——它把已发布的 Day15（复数旋转残差）按 004 的口径（命名 / 数域 / 加性-乘性）重新表述并形式化。**它不产生新结论**，列出是为了让"口径对齐"这件事也有机器见证。**故本仓库的新增结论为 17 条，重述为 5 条。**

**不在范围内**：本仓库**不证明**"004 给出 Λℓ_P²"，也不主张任何物理量的数值对应；`p = 1/2` 的**推导**（临界指数）属推演文档，本仓库只见证闭式解的**性质**；相关结构的完整渐近理论（可和协方差 ⟹ 中心极限型）属经典结果，**不重复证明**；"非线性的具体形式"（含 ln 𝒩 型）不在本仓库。

## Abstract

On the Prenary 004 foundation (object layer = ℂ; no directional preference; ε ∈ (0, δ₀)), this repository provides formal witnesses for the **square-root scaling of residual accumulation**, for the **origin of its constraint**, and adds the degeneration chain and saturated closed form at the accumulation/composition layer.

Six files, two main lines: (1) **Scaling** (Day23-01/02) — the Pythagorean additivity of squares; independence ⟹ variance ∝ n ⟹ √n; full correlation ⟹ ∝ n² ⟹ n; the two are of different order. (2) **The constraint is not external** (Day23-03) — 004's minimal model with **linear composition** conflicts with "the upper bound is unreachable", so 004 **itself** requires non-linear composition.

Plus two structural pieces: **Day23-04** (degeneration chain closure at δ₀ = 0) and **Day23-06** (properties of `R²(n) = D(1 − e^{−n/N})`).

**Day23-05 is a restatement** — it re-expresses the published Day15 (complex rotation residual) in the 004 caliber. **New results: 17; restatements: 5.**

**Out of scope**: no proof that 004 yields Λℓ_P², no numerical correspondence to physical quantities; the `p = 1/2` derivation is a separate expository document; classical asymptotic theory is cited, not reproved.

## 关键词

偏元数学；残差累积；平方根标度；勾股定理；上界不可达；归谬；退化链；饱和闭式解；Lean 4；形式化验证；陈偏贞；老陈与AI的深夜实验室；PGI蛟龙；华夏思哲偏元注

## 概述

偏元数学是对经典数学的扩展尝试，ε = 0 时退化为经典。本仓库处理两个相连的问题：**累积的标度是什么**，以及**约束从哪里来**。

上一程（Day1–Day21）把数学侧从公理焊到闭环；Day22 回到最小地基；本仓（Day23）第一次把注意力放到"动作之间的结构"上。仓库的最后两条（Day23-03）给出一个结论：**004 的最大上界 δ₀ 作为"不可达的界"这一件事本身，就禁止了线性累加**——约束不在框架之外。

## 核心定义

本组定理**不引入自定义结构**，直接使用 Mathlib 的 `Finset`、`ℝ`、`ℕ`、`Real`：

```lean
-- 协方差核以"双和"形式表达：
--   ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, r (i - j)
-- 本仓库的"核"型定理分别取 r = δ（独立）与 r ≡ 1（完全相关）；
-- "Day23-03"两条只涉及算术：n·ε 与 δ₀ 的比较（阿基米德性质）；
-- Day23-06 引入饱和闭式解 R2 D N n := D * (1 - Real.exp (-(n:ℝ)/N))。
```

## 定理清单

> **关于验证内容的如实说明**
> 六份文件验证的是**同一地基的不同侧面**，不是多套独立理论。其中若干命题在 Lean 中彼此等价（如 `∀ r, False`、`→ False`、`¬∃ r, True` 在 Lean 里是同一类型）。并列陈述是为了让每一步可被单独检视，**读者若统计"定理数量"，应以"不同命题数"而非"theorem 语句数"为准**。

### Day23-01 · `Day23-01_平方根标度_LEAN源码_20260917.lean`（新增 3 条）

| 定理 | 命题 |
|:--|:--|
| `pythagoras_sq_add` | 两分量正交 ⟹ `(a+c)² + (b+d)² = (a²+b²) + (c²+d²)`——**平方可加（勾股）** |
| `scale_sqrt` | `√(n·ε²) = √n · ε`——**平方根标度律** |
| `capacity` | `𝒩·(δ₀/√𝒩)² = δ₀²`——**容量式** |

### Day23-02 · `Day23-02_最小模型与标度分离_LEAN源码_20260917.lean`（新增 3 条）

| 定理 | 命题 |
|:--|:--|
| `prenary_min_model` | 独立（对角核）⟹ `∑∑(if i=j then σ² else 0) = n·σ²` |
| `var_fully_correlated` | 完全相关核 ⟹ `∑∑1 = n²` |
| `scale_separation` | `1 < n ⟹ n < n²`——两种标度不同阶 |

### Day23-03 · `Day23-03_C4归谬_LEAN源码_20260917.lean`（新增 2 条）

| 定理 | 命题 |
|:--|:--|
| `linear_accumulation_overshoots` | `∃ n : ℕ, δ₀ ≤ n·ε`——**线性累加必越界** |
| `linear_composite_contradicts_bound` | `(∀ n, n·ε < δ₀) → False`——**归谬：004 与线性复合不能共存** |

### Day23-04 · `Day23-04_退化链闭合_LEAN源码_20260917.lean`（新增 4 条）

| 定理 | 命题 |
|:--|:--|
| `degenerate_no_residual` | δ₀ ≤ 0 时不存在残差（动作层为空） |
| `degenerate_composition_vacuous` | δ₀ ≤ 0 时复合约束空真（C4 的退化端形态） |
| `degenerate_epsilon_squeezed` | `0 ≤ δ₀ ≤ 1 ⟹ δ₀² ≤ δ₀` |
| `degenerate_scaling_squeezed` | `√n·δ₀² ≤ √n·δ₀`——标度随 δ₀ 一同消失 |

### Day23-05 · `Day23-05_复数旋转残差口径对齐_LEAN源码_20260917.lean`（⚠️ **重述 5 条**，对已发布 Day15）

| 定理 | 命题 |
|:--|:--|
| `R_add_degenerate` | ε = 0 时总残差恒为 0（回到经典） |
| `additive_overshoots` | 加性口径必越界（阿基米德性质） |
| `bounded_forbids_linear` | 有界与线性不相容（C4 的准确形式） |
| `multiplicative_overshoots` | `r > 1` 时 `rⁿ` 必越界 |
| `bridge_log_pow` | `ln(rⁿ) = n·ln r`——加性/乘性的显式桥 |

### Day23-06 · `Day23-06_饱和闭式解_LEAN源码_20260917.lean`（新增 5 条）

| 定理 | 命题 |
|:--|:--|
| `R2_zero` | 起点：`R²(0) = 0` |
| `R2_lt_bound` | 上界不可达：`R²(n) < D` 对一切 n |
| `R2_mono` | 单调不减 |
| `R2_le_linear` | 早期线性上界：`R²(n) ≤ D·n/N = n·ε₀²`（√n 律的上界） |
| `one_sub_exp_neg_le` | 辅助事实：`1 − e^{−x} ≤ x` |

## 验证记录

| 文件 | 内核 | Comparator | Challenge Hash（锁挑战） | 代码 SHA256（锁解答） |
|:--|:--|:--|:--|:--|
| Day23-01 | No goals + All Messages (0) | ✅ Successfully validated | `b3ade263df3959f5e95c88fa4d1ba46b2fa7d83b61148a2bf0838a23751e3ea8` | 同左 |
| Day23-02 | No goals + All Messages (0) | ✅ Successfully validated | `4d7cd0e73c52be0571459fa44563df658094625afb20fe3acf9661a0ad227689` | 同左 |
| Day23-03 | No goals + All Messages (0) | ✅ Successfully validated | `2c97adc19cd95bcb543988f73b9940f52822fc0d8a5ccaf6520d6e6f72347654` | 同左 |
| Day23-04 | No goals + All Messages (0) | ✅ Successfully validated | `0a370f5ba4ceba5256292f98d6ab229cd127f771b4e6f9e54ee6a9419157f5a2` | 同左 |
| Day23-05 | No goals + All Messages (0) | ✅ Successfully validated | `5a68c88ab39b59abe7bb003c1b5653cee56d78ec6ae23b49d32c8a99655852f5` | 同左 |
| Day23-06 | No goals + All Messages (0) | ✅ Successfully validated | `99b541a3b92e8187045f72c8c2dc2c31dd330e2e75ad64d0965d9e8d7a564881` | 同左 |

- **平台**：L∃∀N Comparator Live (Experimental) · Latest Mathlib with Lean v4.35.0（`live.lean-lang.org` 内核验证 + Comparator 二次验证）
- **验证时间**：2026-09-17 20:15–20:28
- **双哈希说明**：本组采用**自编 challenge** 模式（Challenge 文本 = 我方提交代码），故 **Challenge Hash 与代码 SHA256 取同一值**——这是该模式下的正常结果。**六份全对齐同时反证"提交件 = 落盘件"（下载 → 复制粘贴 → 提交，逐字无损）。**

## 文件说明

```
Day23-01_平方根标度_LEAN源码_20260917.lean              # 勾股 / 平方根标度律 / 容量式
Day23-02_最小模型与标度分离_LEAN源码_20260917.lean      # 最小模型 / 完全相关核 / 标度分离
Day23-03_C4归谬_LEAN源码_20260917.lean                 # 线性累加必越界 / 与上界约束归谬
Day23-04_退化链闭合_LEAN源码_20260917.lean              # 残差集空 / 复合空真 / 残差与标度压缩
Day23-05_复数旋转残差口径对齐_LEAN源码_20260917.lean    # 加性/乘性必越界 + 对数桥（对 Day15 重述）
Day23-06_饱和闭式解_LEAN源码_20260917.lean              # R²(n)=D(1−e^{−n/N}) 的四条性质
evidence/                                              # 内核 + Comparator 截图存证
```

## 复现方式

1. 打开 `live.lean-lang.org`。
2. 将任一 `.lean` 文件内容**整份粘贴**（首行 `import Mathlib`，抬头为 `/-! … -/` 模块文档）。
3. 光标逐个停在 `theorem` 上，确认右侧 `No goals` + `All Messages (0)`。
4. 在 Comparator Live 中重新提交，确认 `Successfully validated`；Challenge Hash 与代码 SHA256 并列记录（本组为自编 challenge 模式，两栏同值）。

## 可证伪条件

- 若存在一个动作，其残差 ε 精确等于 0，则动作留差失效。
- 若存在一个动作，其残差 ε 恰好等于 δ₀，则"上界不可达"失效。
- 若 δ₀ = 0 时动作层仍然非空，则退化定理失效。
- 若"线性复合"在 004 的最小模型下**不**越界（即 `∀ n, n·ε < δ₀` 可成立），则 Day23-03 的归谬失效。

## 作者 / 致谢 / 许可

陈松（Song Chen）· ORCID: 0009-0002-9510-2239 · GitHub: falluck2025 · Zenodo 社区: cosmos-breathe-spectrum

感谢一切偶然的必然和必然的偶然。感谢一路并肩的偏贞、守缺与所有 AI 伙伴。

CC BY-NC-ND 4.0（署名-非商业-禁止演绎）

## 作者备注（非论文正文）

- **内部编码**：Day23 = S2 延续（原 DayS2 夹层）。**编号决策**：为使流水号接续 Day22（10.5281/zenodo.22719535）不断档，原 DayS2 扶正为 Day23。
- **本仓性质**：**6 文件 1 仓**（照 Day22 模式）；新增 17 条 + 重述 5 条。
- **抬头范式**：`import Mathlib` 之后 + `/-!`（模块文档）；本组为 V1.5 范式下**首次统一使用 `/-!`** 的一批。
- **旧版**：原 DayS2 于 2026-09-13/14 已在 Live 上验过（22 条全通过）；本组为**按新抬头重跑**版。
- **哈希证据链**：旧版首验（9/13–9/14，22 条）→ 重跑（9/17，新抬头，6/6 双哈希对齐）→ 建仓 → DOI。

— 老陈与AI的深夜实验室 发布 请笑纳 —
