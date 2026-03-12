/-
  Hellmann-Feynman 定理

  パラメータ λ に依存するハミルトニアン H(λ) に対して、
  エネルギー固有値の λ 微分は摂動ハミルトニアンの期待値に等しい:

    dE/dλ = ⟨ψ(λ)|∂H/∂λ|ψ(λ)⟩

  ここでは代数的形式で定式化する:
    H₂ = H₁ + δH のとき、⟨ψ₁|H₂|ψ₁⟩ = E₁ + ⟨ψ₁|δH|ψ₁⟩

  これは Hellmann-Feynman 定理の1次摂動論的な表現であり、
  微分形式 dE/dλ = ⟨ψ|∂H/∂λ|ψ⟩ の有限差分版に対応する。
-/
import AutoStudy.DFT.Basic
import AutoStudy.DFT.SelfAdjoint

open MeasureTheory DFT

namespace DFT

/-- パラメータ依存ハミルトニアン系:
    パラメータ λ に対して H(λ), ψ(λ), E(λ) が定義されている -/
structure ParametricSystem where
  /-- パラメータ依存ハミルトニアン -/
  H : ℝ → (ℝ → ℝ) → (ℝ → ℝ)
  /-- パラメータ依存固有状態 -/
  ψ : ℝ → (ℝ → ℝ)
  /-- パラメータ依存固有値（エネルギー） -/
  E : ℝ → ℝ
  /-- 固有状態条件: H(λ)ψ(λ) = E(λ)ψ(λ) -/
  eigenstate : ∀ t, IsEigenstate (H t) (ψ t) (E t)
  /-- 正規化条件: ⟨ψ(λ)|ψ(λ)⟩ = 1 -/
  normalized : ∀ t, IsNormalized (ψ t)

namespace ParametricSystem

variable (sys : ParametricSystem)

/-- 固有値は期待値に等しい: E(t) = ⟨ψ(t)|H(t)|ψ(t)⟩ -/
theorem energy_eq_expectation (t : ℝ) :
    sys.E t = expectationValue (sys.H t) (sys.ψ t) :=
  (eigenstate_expectation_eq (sys.H t) (sys.ψ t) (sys.E t)
    (sys.eigenstate t) (sys.normalized t)).symm

end ParametricSystem

/-- Hellmann-Feynman 定理:
    H₂ = H₁ + δH のとき、⟨ψ₁|H₂|ψ₁⟩ = E₁ + ⟨ψ₁|δH|ψ₁⟩

    物理的意味:
    - H₁ の固有状態 ψ で H₂ の期待値を評価すると、
      元のエネルギー E₁ に摂動 δH の期待値が加わる
    - λ → λ + δλ でハミルトニアンが H → H + (∂H/∂λ)δλ と変化するとき
      E(λ + δλ) ≈ E(λ) + ⟨ψ|∂H/∂λ|ψ⟩δλ -/
theorem hellmann_feynman
    (H₁ : (ℝ → ℝ) → (ℝ → ℝ))
    (δH : (ℝ → ℝ) → (ℝ → ℝ))
    (ψ : ℝ → ℝ) (E₁ : ℝ)
    (heig : IsEigenstate H₁ ψ E₁)
    (hnorm : IsNormalized ψ)
    (H₂ : (ℝ → ℝ) → (ℝ → ℝ))
    (hdecomp : ∀ φ, H₂ φ = fun x => H₁ φ x + δH φ x)
    (hint₁ : Integrable (fun x => ψ x * H₁ ψ x))
    (hint₂ : Integrable (fun x => ψ x * δH ψ x)) :
    expectationValue H₂ ψ = E₁ + expectationValue δH ψ := by
  unfold expectationValue
  have hkey : ∀ x, ψ x * H₂ ψ x = ψ x * H₁ ψ x + ψ x * δH ψ x := by
    intro x
    have := congr_fun (hdecomp ψ) x
    rw [this]; ring
  simp_rw [hkey]
  rw [integral_add hint₁ hint₂]
  rw [show (∫ x, ψ x * H₁ ψ x) = expectationValue H₁ ψ from rfl]
  rw [eigenstate_expectation_eq H₁ ψ E₁ heig hnorm]

/-- Hellmann-Feynman 定理の系: 摂動が定数スカラー倍の場合
    δH ψ = c · ψ のとき ⟨ψ|δH|ψ⟩ = c -/
theorem hellmann_feynman_scalar_perturbation
    (δH : (ℝ → ℝ) → (ℝ → ℝ))
    (ψ : ℝ → ℝ) (c : ℝ)
    (hnorm : IsNormalized ψ)
    (heig_δ : IsEigenstate δH ψ c) :
    expectationValue δH ψ = c :=
  eigenstate_expectation_eq δH ψ c heig_δ hnorm

/-- 2つのハミルトニアンが同じ固有状態を共有し、
    H₂ = H₁ + δH のとき、固有値の関係:
    E₂ = E₁ + ε (ε は δH の固有値) -/
theorem eigenvalue_perturbation
    (H₁ : (ℝ → ℝ) → (ℝ → ℝ))
    (δH : (ℝ → ℝ) → (ℝ → ℝ))
    (ψ : ℝ → ℝ) (E₁ E₂ ε : ℝ)
    (heig₁ : IsEigenstate H₁ ψ E₁)
    (heig_δ : IsEigenstate δH ψ ε)
    (H₂ : (ℝ → ℝ) → (ℝ → ℝ))
    (hdecomp : ∀ φ, H₂ φ = fun x => H₁ φ x + δH φ x)
    (heig₂ : IsEigenstate H₂ ψ E₂)
    (hnorm : IsNormalized ψ) :
    E₂ = E₁ + ε := by
  have hE₂ := eigenstate_expectation_eq H₂ ψ E₂ heig₂ hnorm
  have hE₁ := eigenstate_expectation_eq H₁ ψ E₁ heig₁ hnorm
  have hε := eigenstate_expectation_eq δH ψ ε heig_δ hnorm
  -- ⟨ψ|H₂|ψ⟩ を展開
  have hexp : ∀ x, ψ x * H₂ ψ x = ψ x * H₁ ψ x + ψ x * δH ψ x := by
    intro x
    have := congr_fun (hdecomp ψ) x
    rw [this]; ring
  -- E₂ = ⟨ψ|H₂|ψ⟩ かつ各項を展開
  rw [← hE₂]
  unfold expectationValue
  simp_rw [hexp]
  -- H₁ψ = E₁ψ と δHψ = εψ を代入
  have key₁ : ∀ x, ψ x * H₁ ψ x = E₁ * (ψ x * ψ x) := by
    intro x; have := congr_fun heig₁ x; rw [this]; ring
  have key₂ : ∀ x, ψ x * δH ψ x = ε * (ψ x * ψ x) := by
    intro x; have := congr_fun heig_δ x; rw [this]; ring
  simp_rw [key₁, key₂]
  rw [show (fun x => E₁ * (ψ x * ψ x) + ε * (ψ x * ψ x)) =
      (fun x => (E₁ + ε) * (ψ x * ψ x)) from by ext x; ring]
  rw [integral_const_mul]
  have : innerProduct ψ ψ = 1 := hnorm.norm_eq
  change (E₁ + ε) * ∫ x, ψ x * ψ x = E₁ + ε
  rw [show (∫ x, ψ x * ψ x) = innerProduct ψ ψ from rfl, this, mul_one]

end DFT
