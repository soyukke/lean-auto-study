/-
  √2 の無理数性の証明

  参考: arXiv:2410.14434 "Geometric Proof of the Irrationality of Square-Roots for Select Integers"

  古典的な背理法（無限降下法）による証明:
    √2 = p/q (p, q は互いに素な自然数) と仮定すると
    2q² = p² となり、p は偶数。p = 2k とおくと
    2q² = 4k² → q² = 2k² となり q も偶数。
    これは p, q が互いに素であることに矛盾。
-/
import Mathlib.NumberTheory.Real.Irrational

-- 方法1: Mathlib の既存定理を使う（1行証明）
theorem sqrt_two_irrational : Irrational (√2) :=
  irrational_sqrt_two

-- 方法2: 自然数上で p² = 2 * q² を満たす正の q が存在しないことを
-- 無限降下法で直接証明する
theorem sq_ne_two_mul_sq (p q : ℕ) (hq : q ≠ 0) : p * p ≠ 2 * (q * q) := by
  intro h
  -- p が偶数であることを示す
  have hp_even : 2 ∣ p := by
    have : 2 ∣ p * p := ⟨q * q, by omega⟩
    exact (Nat.Prime.dvd_mul Nat.prime_two).mp this |>.elim id id
  obtain ⟨k, rfl⟩ := hp_even
  -- q が偶数であることを示す
  have hqq : q * q = 2 * (k * k) := by nlinarith
  have hq_even : 2 ∣ q := by
    have : 2 ∣ q * q := ⟨k * k, by omega⟩
    exact (Nat.Prime.dvd_mul Nat.prime_two).mp this |>.elim id id
  obtain ⟨j, rfl⟩ := hq_even
  -- j ≠ 0
  have hj : j ≠ 0 := by omega
  -- k * k = 2 * (j * j) を得る
  have : k * k = 2 * (j * j) := by nlinarith
  -- k < p = 2 * k なので無限降下法で矛盾
  exact absurd this (sq_ne_two_mul_sq k j hj)
termination_by p
decreasing_by
  -- k < 2 * k を示す
  -- k = 0 の場合: p = 0 なので h : 0 = 2 * (q * q) → q = 0 で hq に矛盾
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at h; omega
  · omega
