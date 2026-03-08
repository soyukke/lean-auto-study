/-
  汎関数微分

  汎関数 F[ρ] の密度 ρ に対する変分微分 δF/δρ を定義する。
  Gateaux 微分として定式化:
    d/dε F[ρ + εη]|_{ε=0} = ∫ (δF/δρ)(x) · η(x) dx
-/
import AutoStudy.DFT.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open MeasureTheory DFT

noncomputable section

namespace DFT

/-- 汎関数微分: F[ρ] の ρ に対する変分微分が δF であるとは、
    任意の摂動 η に対して d/dε F[ρ + εη]|_{ε=0} = ⟨δF, η⟩ -/
def HasFunctionalDerivative (F : (ℝ → ℝ) → ℝ) (ρ δF : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, HasDerivAt (fun ε => F (fun x => ρ x + ε * η x)) (innerProduct δF η) 0

/-- 線形汎関数 F[ρ] = ∫ v·ρ の汎関数微分は δF/δρ = v -/
theorem linear_functional_derivative
    (v ρ : ℝ → ℝ)
    (hint : ∀ η : ℝ → ℝ, Integrable (fun x => v x * η x)) :
    HasFunctionalDerivative (fun ρ' => ∫ x, v x * ρ' x) ρ v := by
  intro η
  -- ∫ v(x)·(ρ(x) + ε·η(x)) = (∫ v·ρ) + ε·(∫ v·η)
  have hkey : ∀ ε : ℝ, ∫ x, v x * (ρ x + ε * η x) =
      (∫ x, v x * ρ x) + ε * (∫ x, v x * η x) := by
    intro ε
    have h1 : (fun x => v x * (ρ x + ε * η x)) =
        (fun x => v x * ρ x + ε * (v x * η x)) := by ext x; ring
    have hint2 : Integrable (fun x => ε * (v x * η x)) := by
      have : (fun x => ε * (v x * η x)) = (fun x => v x * (ε * η x)) := by ext x; ring
      rw [this]; exact hint (fun x => ε * η x)
    rw [h1, integral_add (hint ρ) hint2, integral_const_mul]
  simp_rw [hkey]
  -- HasDerivAt for affine function ε ↦ a + ε * b, derivative is b
  have h_mul : HasDerivAt (fun ε : ℝ => ε * (∫ x, v x * η x)) (∫ x, v x * η x) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (∫ x, v x * η x)
  exact h_mul.const_add (∫ x, v x * ρ x)

/-- 定数汎関数 F[ρ] = c の汎関数微分は 0 -/
theorem const_functional_derivative (c : ℝ) (ρ : ℝ → ℝ) :
    HasFunctionalDerivative (fun _ => c) ρ 0 := by
  intro η
  have h0 : innerProduct 0 η = 0 := by
    unfold innerProduct; simp
  rw [h0]
  exact hasDerivAt_const 0 c

/-- 汎関数微分の線形性: δ(F+G)/δρ = δF/δρ + δG/δρ -/
theorem functional_derivative_add
    {F G : (ℝ → ℝ) → ℝ} {ρ δF δG : ℝ → ℝ}
    (hF : HasFunctionalDerivative F ρ δF)
    (hG : HasFunctionalDerivative G ρ δG)
    (hint_F : ∀ η : ℝ → ℝ, Integrable (fun x => δF x * η x))
    (hint_G : ∀ η : ℝ → ℝ, Integrable (fun x => δG x * η x)) :
    HasFunctionalDerivative (fun ρ' => F ρ' + G ρ') ρ (fun x => δF x + δG x) := by
  intro η
  have hsum : innerProduct (fun x => δF x + δG x) η =
      innerProduct δF η + innerProduct δG η := by
    unfold innerProduct
    rw [show (fun x => (δF x + δG x) * η x) =
        (fun x => δF x * η x + δG x * η x) from by ext x; ring]
    exact integral_add (hint_F η) (hint_G η)
  rw [hsum]
  exact (hF η).add (hG η)

/-- 汎関数微分のスカラー倍: δ(cF)/δρ = c · δF/δρ -/
theorem functional_derivative_smul
    {F : (ℝ → ℝ) → ℝ} {ρ δF : ℝ → ℝ} (c : ℝ)
    (hF : HasFunctionalDerivative F ρ δF) :
    HasFunctionalDerivative (fun ρ' => c * F ρ') ρ (fun x => c * δF x) := by
  intro η
  have hprod : innerProduct (fun x => c * δF x) η = c * innerProduct δF η := by
    unfold innerProduct
    rw [show (fun x => c * δF x * η x) = (fun x => c * (δF x * η x)) from by ext x; ring]
    exact integral_const_mul c (fun x => δF x * η x)
  rw [hprod]
  exact (hF η).const_mul c

/-- KS 有効ポテンシャルと汎関数微分の関係 -/
structure KSPotentialFromDerivative where
  E_total : (ℝ → ℝ) → ℝ
  ρ : ℝ → ℝ
  v_eff : ℝ → ℝ
  is_derivative : HasFunctionalDerivative E_total ρ v_eff

end DFT
