/-
  厳密条件 (Exact Constraints)

  交換相関汎関数が満たすべき厳密な数学的条件を定義する。
  新汎関数の「正しさ」はこれらの条件を何個満たすかで評価される。

  主要な厳密条件:
    1. 交換エネルギーの非正性
    2. 相関エネルギーの非正性
    3. Lieb-Oxford 限界
    4. 自己相互作用補正
    5. 交換スケーリング則
    6. 均一密度極限
-/
import AutoStudy.DFT.ExchangeCorrelation
import AutoStudy.DFT.Scaling

open MeasureTheory DFT

namespace DFT

/-- 厳密条件1: 交換エネルギーの非正性
    物理的密度（非負）に対して E_x[ρ] ≤ 0 -/
def IsExchangeNonPositive (E_x : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ, (∀ x, 0 ≤ ρ x) → E_x ρ ≤ 0

/-- 厳密条件2: 相関エネルギーの非正性
    物理的密度に対して E_c[ρ] ≤ 0 -/
def IsCorrelationNonPositive (E_c : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ, (∀ x, 0 ≤ ρ x) → E_c ρ ≤ 0

/-- 厳密条件3: Lieb-Oxford 限界
    E_xc[ρ] ≥ -C · B[ρ] (B は密度から計算される下界) -/
def SatisfiesLiebOxford (E_xc : (ℝ → ℝ) → ℝ) (bound : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ, (∀ x, 0 ≤ ρ x) → bound ρ ≤ E_xc ρ

/-- 厳密条件4: 自己相互作用補正 (SIC)
    1電子系（∫ρ = 1）で E_xc[ρ] = -E_H[ρ] -/
def IsSelfInteractionFree (E_xc E_H : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ, (∀ x, 0 ≤ ρ x) → (∫ x, ρ x = 1) → E_xc ρ = -E_H ρ

-- 厳密条件5: 交換エネルギーのスケーリング則
-- （Scaling.lean の SatisfiesExchangeScaling を参照）

/-- 厳密条件6: 均一密度極限
    一様密度 ρ₀ に対して正しいエネルギー密度を与える -/
def SatisfiesUniformLimit (energyDensity : ℝ → ℝ) (exact_εxc : ℝ → ℝ) : Prop :=
  ∀ ρ₀ > 0, energyDensity ρ₀ = exact_εxc ρ₀

-- メタ定理: 厳密条件間の関係

/-- 交換・相関が共に非正ならば E_xc も非正 -/
theorem xc_nonpositive_of_exchange_correlation (xc : XCFunctional)
    (hx : IsExchangeNonPositive xc.E_x)
    (hc : IsCorrelationNonPositive xc.E_c)
    (ρ : ℝ → ℝ) (hρ : ∀ x, 0 ≤ ρ x) :
    xc.E_xc ρ ≤ 0 := by
  rw [xc.decomposition]
  exact add_nonpos (hx ρ hρ) (hc ρ hρ)

/-- Lieb-Oxford 限界は E_xc の下界を与える -/
theorem lieb_oxford_gives_lower_bound
    {E_xc : (ℝ → ℝ) → ℝ} {bound : (ℝ → ℝ) → ℝ}
    (hLO : SatisfiesLiebOxford E_xc bound)
    (ρ : ℝ → ℝ) (hρ : ∀ x, 0 ≤ ρ x) :
    bound ρ ≤ E_xc ρ :=
  hLO ρ hρ

/-- 非正性と Lieb-Oxford 限界を同時に満たすと E_xc が有界 -/
theorem xc_bounded_of_constraints
    {E_xc : (ℝ → ℝ) → ℝ} {bound : (ℝ → ℝ) → ℝ}
    (hLO : SatisfiesLiebOxford E_xc bound)
    (hNP : ∀ ρ, (∀ x, 0 ≤ ρ x) → E_xc ρ ≤ 0)
    (ρ : ℝ → ℝ) (hρ : ∀ x, 0 ≤ ρ x) :
    bound ρ ≤ E_xc ρ ∧ E_xc ρ ≤ 0 :=
  ⟨hLO ρ hρ, hNP ρ hρ⟩

end DFT
