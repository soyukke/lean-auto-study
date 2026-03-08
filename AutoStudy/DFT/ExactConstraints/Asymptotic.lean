/-
  漸近的性質 (Asymptotic Properties)

  交換相関ポテンシャル v_xc(r) の長距離・短距離での振る舞いに関する厳密条件。

  主要な漸近条件:
    1. v_xc(r) → -1/r (r → ∞、有限系)
    2. 高密度極限での振る舞い (γ → ∞)
    3. 低密度極限での振る舞い (γ → 0)
    4. 急速に変化する密度の極限
-/
import AutoStudy.DFT.ExchangeCorrelation
import AutoStudy.DFT.ExactConstraints
import AutoStudy.DFT.Scaling
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic

open MeasureTheory DFT Filter

noncomputable section

namespace DFT

/-- 漸近条件: v_xc(r) → -1/r (r → ∞)
    有限系における交換相関ポテンシャルの正しい長距離挙動 -/
def HasCorrectAsymptoticDecay (v_xc : ℝ → ℝ) : Prop :=
  Tendsto (fun r => r * v_xc r) atTop (nhds (-1))

/-- 高密度極限 (γ → ∞): 相関エネルギーが交換エネルギーに比べて小さくなる
    E_c[ρ_γ] / E_x[ρ_γ] → 0 as γ → ∞ -/
def CorrelationVanishesInHighDensity (E_x E_c : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ, E_x ρ ≠ 0 →
    Tendsto (fun γ => E_c (scaledDensity γ ρ) / E_x (scaledDensity γ ρ)) atTop (nhds 0)

/-- 高密度極限でのスケーリング:
    交換が E_x[ρ_γ] = γ E_x[ρ] を満たすなら、
    γ → ∞ で E_c は E_x より遅く成長する -/
theorem high_density_scaling_implication
    {E_x E_c : (ℝ → ℝ) → ℝ}
    (hscale : SatisfiesExchangeScaling E_x)
    (hcorr : CorrelationVanishesInHighDensity E_x E_c)
    (ρ : ℝ → ℝ) (hEx : E_x ρ ≠ 0) :
    Tendsto (fun γ => E_c (scaledDensity γ ρ) / (γ * E_x ρ)) atTop (nhds 0) := by
  have h := hcorr ρ hEx
  -- E_x[ρ_γ] = γ E_x[ρ] なので、γ > 0 で二つの式は一致
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with γ hγ
  congr 1
  exact hscale γ hγ ρ

/-- 低密度極限 (γ → 0+): 交換相関が交換に支配される
    E_xc[ρ_γ] / E_x[ρ_γ] → 1 as γ → 0+ -/
def ExchangeDominatesLowDensity (E_x E_xc : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ ρ, (∀ γ > 0, E_x (scaledDensity γ ρ) ≠ 0) →
    Tendsto (fun γ => E_xc (scaledDensity γ ρ) / E_x (scaledDensity γ ρ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

/-- スピン分極に対する条件:
    完全分極系と非分極系の間の正しい関係 -/
def SatisfiesSpinScaling (E_x : (ℝ → ℝ) → ℝ) (spinFactor : ℝ) : Prop :=
  ∀ ρ, (∀ x, 0 ≤ ρ x) →
    E_x (fun x => 2 * ρ x) = spinFactor * E_x ρ

/-- 均一座標スケーリングに対する相関エネルギーの上界:
    E_c[ρ_γ] ≤ E_c[ρ] for γ ≥ 1
    (相関は高密度で弱まる) -/
def CorrelationDecreaseUnderScaling (E_c : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ γ ≥ 1, ∀ ρ, (∀ x, 0 ≤ ρ x) → E_c (scaledDensity γ ρ) ≤ E_c ρ

/-- 相関がスケーリングで減少し、非正であれば、
    スケーリングされた密度での相関も非正 -/
theorem scaled_correlation_nonpositive
    {E_c : (ℝ → ℝ) → ℝ}
    (hNP : IsCorrelationNonPositive E_c)
    (γ : ℝ) (hγ : 0 < γ)
    (ρ : ℝ → ℝ) (hρ : ∀ x, 0 ≤ ρ x) :
    E_c (scaledDensity γ ρ) ≤ 0 :=
  hNP (scaledDensity γ ρ) (scaledDensity_nonneg hγ hρ)

end DFT
