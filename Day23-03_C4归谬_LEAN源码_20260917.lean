import Mathlib

/-! ================================================================
   偏元数学 · 新线 S2 · C4 的归谬（Day23-03）
   ------------------------------------------------------------------
   核心：在 004 的最小模型下，若"复合"取线性累加 R_n = n·ε，
         则存在 n 使 R_n ≥ δ₀ —— 与 004「ε < δ₀（上界不可达）」冲突。
         故 004 自身要求"复合不能线性累加"，这就是 C4（不撞）。
   本稿范围：只形式化"线性累加 ⟹ 必越界"的算术核心（阿基米德性质），共 2 条。
   不做：不处理"非线性的具体形式"（那是 C5 / B1-2 的范围）。
   注：本件为 Day23 第 3 份（原 S2 · 2 级 A 方向-丁补）；
       上承 Day22 prenary-math-lean-s2-action-foundation
       （10.5281/zenodo.22719535）。
   日期：2026-09-17（重跑版）
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

-- ① 线性累加必越界：对任意 δ₀，存在 n 使 n·ε ≥ δ₀
--    取 n = ⌈δ₀/ε⌉ 即可（实数的阿基米德性质）
theorem linear_accumulation_overshoots (δ0 ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, δ0 ≤ (n : ℝ) * ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (δ0 / ε)
  refine ⟨n, ?_⟩
  have h1 : (δ0 / ε) * ε < (n : ℝ) * ε := mul_lt_mul_of_pos_right hn hε
  have h2 : (δ0 / ε) * ε = δ0 := div_mul_cancel₀ δ0 (ne_of_gt hε)
  linarith

-- ② 归谬：若"线性复合的总残差始终 < δ₀"，则矛盾
--    ⟹ 004「上界不可达」与线性复合不能共存
--    ⟹ C4（不撞）是 004 的自洽性要求，不是外接假设
theorem linear_composite_contradicts_bound (δ0 ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ n : ℕ, (n : ℝ) * ε < δ0) : False := by
  obtain ⟨n, hn⟩ := exists_nat_gt (δ0 / ε)
  have h1 : (δ0 / ε) * ε < (n : ℝ) * ε := mul_lt_mul_of_pos_right hn hε
  have h2 : (δ0 / ε) * ε = δ0 := div_mul_cancel₀ δ0 (ne_of_gt hε)
  have h3 := hbound n
  linarith
