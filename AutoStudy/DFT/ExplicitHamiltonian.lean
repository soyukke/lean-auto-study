/-
  明示的ハミルトニアン

  DFT の外部ポテンシャル依存を明示するため、
  H = T + V_ext + V_ee の形を持つハミルトニアンを定義する。
  これにより Hohenberg-Kohn 第一定理で使う期待値差を
  外部ポテンシャル差の密度積分から導出できる。
-/
import AutoStudy.DFT.Basic

open MeasureTheory

namespace DFT

/-- 外部ポテンシャルによる 1 体演算子: (Vψ)(x) = v(x) ψ(x) -/
def externalOperator (v : ℝ → ℝ) : (ℝ → ℝ) → (ℝ → ℝ) :=
  fun ψ x => v x * ψ x

/-- 外部ポテンシャルのエネルギー寄与 ∫ v(x) ρ(x) dx -/
noncomputable def externalEnergy (v ψ : ℝ → ℝ) : ℝ :=
  expectationValue (externalOperator v) ψ

/-- H = T + V_ext + V_ee の形を持つ明示的ハミルトニアン -/
structure ExplicitHamiltonian where
  kinetic : (ℝ → ℝ) → (ℝ → ℝ)
  vExt : ℝ → ℝ
  interaction : (ℝ → ℝ) → (ℝ → ℝ)

namespace ExplicitHamiltonian

/-- 明示的ハミルトニアンに対応する演算子 -/
def toOperator (H : ExplicitHamiltonian) : (ℝ → ℝ) → (ℝ → ℝ) :=
  fun ψ x => H.kinetic ψ x + H.vExt x * ψ x + H.interaction ψ x

/-- 期待値分解に必要な可積分性条件 -/
structure IntegrableState (H : ExplicitHamiltonian) (ψ : ℝ → ℝ) : Prop where
  kinetic : Integrable (fun x => ψ x * H.kinetic ψ x)
  external : Integrable (fun x => H.vExt x * electronDensity ψ x)
  interaction : Integrable (fun x => ψ x * H.interaction ψ x)

/-- 外部ポテンシャル項の期待値は ∫ vρ -/
theorem externalEnergy_eq (v ψ : ℝ → ℝ) :
    externalEnergy v ψ = ∫ x, v x * electronDensity ψ x := by
  unfold externalEnergy expectationValue externalOperator electronDensity
  congr 1
  ext x
  ring

/-- 明示的ハミルトニアンの作用を点ごとに展開 -/
theorem toOperator_apply (H : ExplicitHamiltonian) (ψ : ℝ → ℝ) (x : ℝ) :
    H.toOperator ψ x = H.kinetic ψ x + H.vExt x * ψ x + H.interaction ψ x :=
  rfl

/-- 期待値は運動 + 外部 + 相互作用に分解される -/
theorem expectation_decomposition (H : ExplicitHamiltonian) (ψ : ℝ → ℝ)
    (hint : H.IntegrableState ψ) :
    expectationValue H.toOperator ψ =
      expectationValue H.kinetic ψ +
        externalEnergy H.vExt ψ + expectationValue H.interaction ψ := by
  have hExt' : Integrable (fun x => ψ x * (H.vExt x * ψ x)) := by
    have hEq : (fun x => ψ x * (H.vExt x * ψ x)) =
        (fun x => H.vExt x * electronDensity ψ x) := by
      ext x
      unfold electronDensity
      ring
    rw [hEq]
    exact hint.external
  have hRest : Integrable (fun x => ψ x * (H.vExt x * ψ x) + ψ x * H.interaction ψ x) :=
    hExt'.add hint.interaction
  unfold expectationValue toOperator
  have hExpand :
      (fun x => ψ x * (H.kinetic ψ x + H.vExt x * ψ x + H.interaction ψ x)) =
      (fun x => ψ x * H.kinetic ψ x + (ψ x * (H.vExt x * ψ x) + ψ x * H.interaction ψ x)) := by
    ext x
    ring
  have hExtVal : ∫ x, ψ x * (H.vExt x * ψ x) = ∫ x, H.vExt x * electronDensity ψ x := by
    congr 1
    ext x
    unfold electronDensity
    ring
  rw [hExpand, integral_add hint.kinetic hRest,
    integral_add hExt' hint.interaction, externalEnergy_eq]
  rw [hExtVal]
  ring

/-- 外部エネルギーはポテンシャル差で差をとれる -/
theorem externalEnergy_sub (v₁ v₂ ψ : ℝ → ℝ)
    (hint₁ : Integrable (fun x => v₁ x * electronDensity ψ x))
    (hint₂ : Integrable (fun x => v₂ x * electronDensity ψ x)) :
    externalEnergy (fun x => v₁ x - v₂ x) ψ = externalEnergy v₁ ψ - externalEnergy v₂ ψ := by
  repeat rw [externalEnergy_eq]
  have hEq : (fun x => (v₁ x - v₂ x) * electronDensity ψ x) =
      (fun x => v₁ x * electronDensity ψ x - v₂ x * electronDensity ψ x) := by
    ext x
    ring
  rw [hEq, integral_sub hint₁ hint₂]

/-- 運動項と相互作用項が共通なら、期待値差は外部ポテンシャル差のみで決まる -/
theorem expectation_difference_of_same_core
    (H₁ H₂ : ExplicitHamiltonian) (ψ : ℝ → ℝ)
    (hKinetic : H₁.kinetic = H₂.kinetic)
    (hInteraction : H₁.interaction = H₂.interaction)
    (hint₁ : H₁.IntegrableState ψ)
    (hint₂ : H₂.IntegrableState ψ) :
    expectationValue H₁.toOperator ψ - expectationValue H₂.toOperator ψ =
      externalEnergy
        (fun x => H₁.vExt x - H₂.vExt x) ψ := by
  rw [H₁.expectation_decomposition ψ hint₁, H₂.expectation_decomposition ψ hint₂]
  rw [hKinetic, hInteraction]
  rw [externalEnergy_sub (fun x => H₁.vExt x) (fun x => H₂.vExt x) ψ hint₁.external hint₂.external]
  ring

end ExplicitHamiltonian

end DFT
