import Mathlib

/-! ================================================================
   偏元数学 · 新线 S2 · 最小模型、完全相关核与标度分离（Day23-02）
   ------------------------------------------------------------------
   核心：最小模型（ε 逐次独立同分布、协方差非对角为 0）的双和 = n·σ²
         ⟹ 方差 ∝ n ⟹ α = 1/2；
         完全相关核（r ≡ 1）的双和 = n² ⟹ 方差 ∝ n² ⟹ α = 1；
         故 n < n²（n > 1）—— 两种标度是【不同阶】。
   本稿范围：三条代数恒等式（核 → 方差 → 标度），共 3 条。
   不做：不涉及"核的具体来源"；不主张任何物理量的数值对应。
   注：本件为 Day23 第 2 份（原 S2 · 2 级门票 · A 方向-丁 v3）；
       上承 Day22 prenary-math-lean-s2-action-foundation
       （10.5281/zenodo.22719535）。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

-- 修订记录（v3 定版）：
--   v1: ① 停在 "∑ x ∈ range n, if x < n then σ2 else 0"；② 停在 "↑n * ↑n = ↑n ^ 2"；③ 已通过
--   v2: ① 改用 sum_eq_single，但用 rw 传参（副目标顺序不可靠）
--   v3: ① 改为【显式传参】Finset.sum_eq_single i h1 h2，绕开副目标顺序问题
--       ② 补 ring 收尾

-- ① 接 004：最小模型（ε 逐次独立同分布、方差 σ²）
--    协方差矩阵非对角元为 0 ⟹ 双和退化为 n 项 ⟹ 方差 ∝ n ⟹ α = 1/2
theorem prenary_min_model (n : ℕ) (σ2 : ℝ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (if i = j then σ2 else (0 : ℝ))) = (n : ℝ) * σ2 := by
  have h : ∀ i ∈ Finset.range n,
      (∑ j ∈ Finset.range n, (if i = j then σ2 else (0 : ℝ))) = σ2 := by
    intro i hi
    have h1 : ∀ b ∈ Finset.range n, b ≠ i → (if i = b then σ2 else (0 : ℝ)) = 0 := by
      intro b _ hb
      simp [Ne.symm hb]
    have h2 : i ∉ Finset.range n → (if i = i then σ2 else (0 : ℝ)) = 0 := by
      intro hc
      exact absurd hi hc
    rw [Finset.sum_eq_single i h1 h2]
    simp
  calc (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (if i = j then σ2 else (0 : ℝ)))
      = ∑ _i ∈ Finset.range n, σ2 := Finset.sum_congr rfl h
    _ = (n : ℝ) * σ2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

-- ② 完全相关核（r_k ≡ 1）⟹ 双和 = n² ⟹ 方差 ∝ n² ⟹ α = 1
theorem var_fully_correlated (n : ℕ) :
    (∑ _i ∈ Finset.range n, ∑ _j ∈ Finset.range n, (1 : ℝ)) = (n : ℝ) ^ 2 := by
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

-- ③ 标度分离：n < n²（n > 1）
--    ⟹ "独立"的 √n 量级与"完全相关"的 n 量级是【不同阶】
theorem scale_separation (n : ℕ) (h : 1 < n) : (n : ℝ) < (n : ℝ) ^ 2 := by
  have hn : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h
  nlinarith
