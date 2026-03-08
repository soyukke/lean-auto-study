/-
  サイズ整合性と追加の厳密条件

  汎関数が満たすべき追加の物理的条件:
    1. サイズ整合性: 無限に離れた2つの系のエネルギーは加法的
    2. 座標変換不変性: 並進・回転に対する不変性
    3. 非一様スケーリング不等式
    4. 凸性条件
-/
import AutoStudy.DFT.ExchangeCorrelation
import AutoStudy.DFT.ExactConstraints

open MeasureTheory DFT

noncomputable section

namespace DFT

/-- サイズ整合性:
    ρ = ρ_A + ρ_B（重なりなし）のとき E_xc[ρ] = E_xc[ρ_A] + E_xc[ρ_B]
    ここでは台が重ならない密度に対して定義 -/
def IsSizeConsistent (E_xc : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ_A ρ_B : ℝ → ℝ,
    (∀ x, 0 ≤ ρ_A x) → (∀ x, 0 ≤ ρ_B x) →
    (∀ x, ρ_A x = 0 ∨ ρ_B x = 0) →  -- 台が重ならない
    E_xc (fun x => ρ_A x + ρ_B x) = E_xc ρ_A + E_xc ρ_B

/-- 局所汎関数はサイズ整合的 -/
theorem local_functional_size_consistent (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hint_A : ∀ ρ_A : ℝ → ℝ, Integrable (fun x => f (ρ_A x)))
    (hint_B : ∀ ρ_B : ℝ → ℝ, Integrable (fun x => f (ρ_B x))) :
    IsSizeConsistent (localFunctionalEnergy f) := by
  intro ρ_A ρ_B _ _ hdisjoint
  unfold localFunctionalEnergy
  have hsum : (fun x => f (ρ_A x + ρ_B x)) = (fun x => f (ρ_A x) + f (ρ_B x)) := by
    ext x
    cases hdisjoint x with
    | inl h => rw [h, zero_add, hf0, zero_add]
    | inr h => rw [h, add_zero, hf0, add_zero]
  rw [hsum, integral_add (hint_A ρ_A) (hint_B ρ_B)]

/-- 並進不変性: E_xc[ρ(· - a)] = E_xc[ρ] -/
def IsTranslationInvariant (E_xc : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ : ℝ → ℝ, ∀ a : ℝ, E_xc (fun x => ρ (x - a)) = E_xc ρ

/-- 凸性条件: t ∈ [0,1] に対して
    E_xc[t·ρ₁ + (1-t)·ρ₂] ≤ t·E_xc[ρ₁] + (1-t)·E_xc[ρ₂]
    (厳密には交換エネルギーは凸) -/
def IsConvex (E : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ₁ ρ₂ : ℝ → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    E (fun x => t * ρ₁ x + (1 - t) * ρ₂ x) ≤ t * E ρ₁ + (1 - t) * E ρ₂

/-- 凸性と非正性から、混合密度でも非正 -/
theorem convex_nonpositive_mixed
    {E : (ℝ → ℝ) → ℝ}
    (hconv : IsConvex E)
    (hNP : ∀ ρ, (∀ x, 0 ≤ ρ x) → E ρ ≤ 0)
    (ρ₁ ρ₂ : ℝ → ℝ) (hρ₁ : ∀ x, 0 ≤ ρ₁ x) (hρ₂ : ∀ x, 0 ≤ ρ₂ x)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    E (fun x => t * ρ₁ x + (1 - t) * ρ₂ x) ≤ 0 := by
  calc E (fun x => t * ρ₁ x + (1 - t) * ρ₂ x)
      _ ≤ t * E ρ₁ + (1 - t) * E ρ₂ := hconv ρ₁ ρ₂ t ht0 ht1
      _ ≤ t * 0 + (1 - t) * 0 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hNP ρ₁ hρ₁) ht0
          · exact mul_le_mul_of_nonneg_left (hNP ρ₂ hρ₂) (by linarith)
      _ = 0 := by ring

/-- 正の同次性: E[t·ρ] = t^d · E[ρ] (t > 0)
    交換エネルギーは次数 4/3 で同次だが、
    一般的な同次性として定義（次数は自然数） -/
def IsPositivelyHomogeneous (E : (ℝ → ℝ) → ℝ) (degree : ℕ) : Prop :=
  ∀ t > 0, ∀ ρ : ℝ → ℝ, E (fun x => t * ρ x) = t ^ degree * E ρ

/-- 正の同次な汎関数は E[0] = 0 -/
theorem homogeneous_zero {E : (ℝ → ℝ) → ℝ} {d : ℕ}
    (hd : 0 < d) (hhom : IsPositivelyHomogeneous E d) :
    E (fun _ => 0) = 0 := by
  have h := hhom 2 (by norm_num) (fun _ => 0)
  simp only [mul_zero] at h
  -- h : E (fun _ => 0) = (2:ℝ) ^ d * E (fun _ => 0)
  have h1 : (1 : ℝ) < (2 : ℝ) ^ d :=
    one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega)
  by_contra hne
  have h2 : (2 : ℝ) ^ d = 1 :=
    mul_right_cancel₀ hne (show (2 : ℝ) ^ d * E (fun _ => 0) = 1 * E (fun _ => 0) by
      rw [one_mul]; linarith)
  linarith

end DFT
