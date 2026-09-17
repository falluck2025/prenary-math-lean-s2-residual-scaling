import Mathlib

/-! ================================================================
   偏元数学 · 新线 S2 · 累积与复合支 · 退化链闭合（Day23-04）
   ------------------------------------------------------------------
   核心：δ₀ = 0（赋值退化）时，本支的全部构件同时消失——
         残差集空 → 复合约束空真 → 标度被压缩归零。
         即【δ₀ 是本支唯一的尺度参数】。
   本稿范围：只证"退化链闭合"这一件事，共 4 条。
   不做：不涉及 δ₀ > 0 时的任何非平凡结论。
   注：004 定理 1 给出"单次"退化；本件补"累积与复合"这一层的退化。
       本件为 Day23 第 4 份；上承 Day22 prenary-math-lean-s2-action-foundation
       （10.5281/zenodo.22719535）。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

-- e-① 退化·残差集空：δ₀ ≤ 0 时不存在残差（动作层为空）
theorem degenerate_no_residual {δ0 : ℝ} (h : δ0 ≤ 0) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ε < δ0 := by
  rintro ⟨ε, hpos, hlt⟩
  linarith

-- e-② 退化·复合约束空真：δ₀ ≤ 0 时，"总残差仍在动作层内"无实例可违反
--     （这是 C4 复合封闭在退化端的形态）
theorem degenerate_composition_vacuous {δ0 : ℝ} (h : δ0 ≤ 0) :
    ∀ R : ℝ, 0 < R → R < δ0 → False := by
  intro R hpos hlt
  linarith

-- e-③ 退化·残差被压缩：ε = δ₀² 时，0 ≤ δ₀ ≤ 1 ⟹ ε ≤ δ₀
--     （δ₀ 越小，单步残差压得越低——退化不是"慢慢归零"，而是"两头一起塌"）
theorem degenerate_epsilon_squeezed {δ0 : ℝ} (h0 : 0 ≤ δ0) (h1 : δ0 ≤ 1) :
    δ0 ^ 2 ≤ δ0 := by
  nlinarith

-- e-④ 退化·标度被压缩：R_n = √n·δ₀² ≤ √n·δ₀（标度随 δ₀ 一同消失）
theorem degenerate_scaling_squeezed (n : ℕ) {δ0 : ℝ} (h0 : 0 ≤ δ0) (h1 : δ0 ≤ 1) :
    Real.sqrt n * δ0 ^ 2 ≤ Real.sqrt n * δ0 := by
  exact mul_le_mul_of_nonneg_left (degenerate_epsilon_squeezed h0 h1) (Real.sqrt_nonneg n)
