import Mathlib

/-! ================================================================
   偏元数学 · 新线 S2 · Day15-S2 · 复数旋转残差：口径对齐（Day23-05）
   ------------------------------------------------------------------
   上游：NEW(S)-004 偏元数学地基定稿（定义 2：0 < ε < δ₀；公理 1：op = op₀ + ε）
   由来：Day15（2026-09-02，晚于 004 钉版、早于 004 定稿）与 004 定稿
         之间存在三处口径差，本稿按 004 口径重述。
   三处对齐：
     ① 命名统一：θ = 旋转角（Day15 原称 ε）；ε = 残差（∈ (0, δ₀)）
     ② 数域桥接：Day15 的复参数 r = |r|·e^{iφ} 拆为「模 |r|」+「相位 φ」
                （模对应实残差 ε，相位对应旋转角 θ；见证留给后续）
     ③ 加性/乘性：乘性累积 rⁿ 取对数后等价于加性 n·ln r
   核心结论（C4 的准确形式）：加性口径与乘性口径都必越界
         ⟹ 「复合封闭」与这两种口径都不相容。共 5 条。
   不做：⚠️ 不主张"004 蕴含 C4"；只主张"若约定复合封闭，则线性被排除"。
   注：⚠️ 本件是"对已发布 Day15 的口径重述"，**不是新结论**；
       本件为 Day23 第 5 份；上承 Day22 prenary-math-lean-s2-action-foundation
       （10.5281/zenodo.22719535）。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

open Filter

noncomputable section

/-- 加性口径：连续 n 次动作后的总残差 -/
def R_add (ε : ℝ) (n : ℕ) : ℝ := (n : ℝ) * ε

/-- 退化：ε = 0 时总残差恒为 0（回到经典） -/
theorem R_add_degenerate (n : ℕ) : R_add 0 n = 0 := by
  unfold R_add
  simp

/-- ① 加性口径必越界：只要 ε > 0，总残差迟早超过任意上界 δ₀（阿基米德性质） -/
theorem additive_overshoots (δ0 ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, δ0 ≤ R_add ε n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (δ0 / ε)
  refine ⟨n, ?_⟩
  unfold R_add
  rw [div_lt_iff₀ hε] at hn
  linarith

/-- ② C4 的准确形式：若约定复合后的总残差恒有界（Rₙ < δ₀ 对一切 n），
    则复合不可能是线性累加。此为「有界」与「线性」的不相容。 -/
theorem bounded_forbids_linear (δ0 ε : ℝ) (hε : 0 < ε) :
    ¬ (∀ n : ℕ, R_add ε n < δ0) := by
  intro h
  obtain ⟨n, hn⟩ := additive_overshoots δ0 ε hε
  exact absurd (h n) (not_lt.mpr hn)

/-- ③ 乘性口径同样必越界：r > 1 时 rⁿ 迟早超过任意上界 -/
theorem multiplicative_overshoots (r : ℝ) (hr : 1 < r) (δ0 : ℝ) :
    ∃ n : ℕ, δ0 ≤ r ^ n := by
  have h : Tendsto (fun n : ℕ => r ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  exact (h.eventually (eventually_ge_atTop δ0)).exists

/-- ④ 加性-乘性的显式桥：取对数后，乘性累积 = 加性累积 -/
theorem bridge_log_pow (r : ℝ) (n : ℕ) :
    Real.log (r ^ n) = (n : ℝ) * Real.log r := by
  rw [Real.log_pow]

end
