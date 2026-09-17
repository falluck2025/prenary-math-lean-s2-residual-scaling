import Mathlib

/-! ================================================================
   偏元数学 · 新线 S2 · 饱和闭式解 · 临界反馈指数 p = 1/2（Day23-06）
   ------------------------------------------------------------------
   承接：2026-09-13 晚推演链（双鱼 → 反馈 → 截断 → p ≥ 1/2 → p = 1/2）
   上游：004（定义 2；公理 1）、C4（复合封闭）、C5（均方守恒 Σεₖ² = δ₀²）
   闭式解：R_n² = D (1 − e^{−n/N})，其中 D = δ₀²，N = 𝒩 = D/ε₀²
   本稿见证四条：
     ① 起点：R²(0) = 0
     ② 上界不可达：R²(n) < D 对一切 n
     ③ 单调不减
     ④ 早期线性上界：R²(n) ≤ D·n/N = n·ε₀²（√n 律的上界）
   辅助事实：1 − e^{−x} ≤ x（它是 ④ 的来源，也是"√n 是上界"的来源）。共 5 条。
   不做：不推导 p = 1/2 本身（那是推演文档）；本件只见证闭式解的性质。
   注：本件为 Day23 第 6 份；上承 Day22 prenary-math-lean-s2-action-foundation
       （10.5281/zenodo.22719535）。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

noncomputable section

/-- 饱和闭式解 R²（归一化：D = δ₀²，N = 𝒩） -/
def R2 (D N : ℝ) (n : ℕ) : ℝ := D * (1 - Real.exp (-(n : ℝ) / N))

/-- 辅助事实：1 - e^{-x} ≤ x（对一切实数 x 成立） -/
theorem one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- ① 起点：R²(0) = 0 -/
theorem R2_zero (D N : ℝ) : R2 D N 0 = 0 := by
  unfold R2
  simp

/-- ② 上界不可达：R²(n) < D 对一切 n -/
theorem R2_lt_bound (D N : ℝ) (hD : 0 < D) (n : ℕ) : R2 D N n < D := by
  unfold R2
  have h : 0 < D * Real.exp (-(n : ℝ) / N) := mul_pos hD (Real.exp_pos _)
  nlinarith

/-- ③ 单调不减 -/
theorem R2_mono (D N : ℝ) (hD : 0 ≤ D) (hN : 0 < N) {m n : ℕ} (hmn : m ≤ n) :
    R2 D N m ≤ R2 D N n := by
  unfold R2
  have h1 : Real.exp (-(n : ℝ) / N) ≤ Real.exp (-(m : ℝ) / N) := by
    rw [Real.exp_le_exp]
    rw [neg_div, neg_div]
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have h2 : (m : ℝ) / N ≤ (n : ℝ) / N := div_le_div_of_nonneg_right hmn' hN.le
    linarith
  exact mul_le_mul_of_nonneg_left (by linarith) hD

/-- ④ 早期线性上界：R²(n) ≤ D·n/N = n·ε₀²（√n 律的上界） -/
theorem R2_le_linear (D N : ℝ) (hD : 0 ≤ D) (n : ℕ) :
    R2 D N n ≤ D * ((n : ℝ) / N) := by
  unfold R2
  rw [neg_div]
  exact mul_le_mul_of_nonneg_left (one_sub_exp_neg_le ((n : ℝ) / N)) hD

end
