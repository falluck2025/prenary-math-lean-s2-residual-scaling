import Mathlib

/-! ================================================================
   偏元数学 · 新线 S2 · 残差累积的平方根标度及其约束（Day23-01）
   ------------------------------------------------------------------
   核心：√(n·ε²) = √n·ε —— 平方可加的根据是正交（勾股）；
         容量式 𝒩·(δ₀/√𝒩)² = δ₀²。
   本稿范围：勾股（正交 ⟹ 平方可加）/ 平方根标度律 / 容量式，共 3 条。
   不做：不证"004 给出 Λℓ_P²"；不主张任何物理量的数值对应；
         不重复经典渐近理论（可和协方差 ⟹ 中心极限型，另注出处）。
   注：Day23 = S2 延续（原 DayS2 夹层）第 1 份，按新抬头范式重跑；
       上承 Day22 prenary-math-lean-s2-action-foundation
       （10.5281/zenodo.22719535）。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

-- 定理1：勾股 —— 两分量正交 ⟹ 平方可加
theorem pythagoras_sq_add (a b c d : ℝ) (h : a * c + b * d = 0) :
    (a + c) ^ 2 + (b + d) ^ 2 = (a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) := by
  nlinarith [h]

-- 定理2：平方根标度律 —— √(n·ε²) = √n · ε
theorem scale_sqrt (n : ℕ) (eps : ℝ) (h : 0 < eps) :
    Real.sqrt (n * eps ^ 2) = Real.sqrt n * eps := by
  rw [Real.sqrt_mul (Nat.cast_nonneg n) (eps ^ 2), Real.sqrt_sq (le_of_lt h)]

-- 定理3：容量式 —— 𝒩·(δ₀/√𝒩)² = δ₀²
theorem capacity (delta0 : ℝ) (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * (delta0 / Real.sqrt N) ^ 2 = delta0 ^ 2 := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (le_of_lt hN')
  field_simp
  rw [hs]
  ring
