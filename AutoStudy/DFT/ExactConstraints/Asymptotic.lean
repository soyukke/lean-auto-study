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

-- ============================================================
-- 局所ポテンシャルの漸近的限界
-- ============================================================

/-- 局所ポテンシャルの定義: v(r) = f(ρ(r)) -/
def IsLocalPotential (v : ℝ → ℝ) (f : ℝ → ℝ) (ρ : ℝ → ℝ) : Prop :=
  ∀ r, v r = f (ρ r)

/-- 正の極限を持つポテンシャルは -1/r 減衰を持てない:
    v(r) → L > 0 のとき、r * v(r) > 0 (十分大きい r で) なので -1 に収束しない -/
theorem not_asymptotic_of_tendsto_pos {v : ℝ → ℝ} {L : ℝ}
    (hv : Tendsto v atTop (nhds L)) (hL : 0 < L) :
    ¬ HasCorrectAsymptoticDecay v := by
  intro hasym
  have h1 : ∀ᶠ r in atTop, r * v r < 0 :=
    (tendsto_order.mp hasym).2 0 (by norm_num)
  have h2 : ∀ᶠ r in atTop, 0 < v r :=
    (tendsto_order.mp hv).1 0 hL
  have h3 := h1.and (h2.and (eventually_gt_atTop 0))
  rcases h3.exists with ⟨r, hr1, hr2, hr3⟩
  linarith [mul_pos hr3 hr2]

/-- 負の極限を持つポテンシャルは -1/r 減衰を持てない:
    v(r) → L < 0 のとき、r * v(r) → -∞ なので -1 に収束しない -/
theorem not_asymptotic_of_tendsto_neg {v : ℝ → ℝ} {L : ℝ}
    (hv : Tendsto v atTop (nhds L)) (hL : L < 0) :
    ¬ HasCorrectAsymptoticDecay v := by
  intro hasym
  have h1 : ∀ᶠ r in atTop, -2 < r * v r :=
    (tendsto_order.mp hasym).1 (-2) (by norm_num)
  have h2 : ∀ᶠ r in atTop, v r < L / 2 :=
    (tendsto_order.mp hv).2 (L / 2) (by linarith)
  have hLneg : (0 : ℝ) < -L := neg_pos.mpr hL
  have h3 : ∀ᶠ r in atTop, 4 / (-L) < r :=
    eventually_gt_atTop (4 / (-L))
  have h4 := h1.and (h2.and h3)
  rcases h4.exists with ⟨r, hr1, hr2, hr3⟩
  have hrpos : 0 < r := lt_trans (div_pos (by norm_num) hLneg) hr3
  have hL2 : L / 2 < 0 := by linarith
  have hr4 : r * v r < -2 :=
    calc r * v r
        ≤ r * (L / 2) := mul_le_mul_of_nonneg_left (le_of_lt hr2) (le_of_lt hrpos)
      _ < 4 / (-L) * (L / 2) := mul_lt_mul_of_neg_right hr3 hL2
      _ = -2 := by field_simp [ne_of_lt hL]; ring
  linarith

/-- 非零極限を持つポテンシャルは -1/r 減衰を持てない -/
theorem not_asymptotic_of_tendsto_ne_zero {v : ℝ → ℝ} {L : ℝ}
    (hv : Tendsto v atTop (nhds L)) (hL : L ≠ 0) :
    ¬ HasCorrectAsymptoticDecay v := by
  rcases lt_or_gt_of_ne hL with h | h
  · exact not_asymptotic_of_tendsto_neg hv h
  · exact not_asymptotic_of_tendsto_pos hv h

/-- 局所ポテンシャルの漸近的限界:
    f が連続で f(0) ≠ 0、密度が減衰するならば -1/r 減衰を持てない。
    LDA/GGA のポテンシャルが正しい漸近挙動を持てない根本的理由。 -/
theorem local_potential_no_asymptotic_decay
    (f : ℝ → ℝ) (ρ : ℝ → ℝ)
    (hf : ContinuousAt f 0) (hf0 : f 0 ≠ 0)
    (hρ : Tendsto ρ atTop (nhds 0)) :
    ¬ HasCorrectAsymptoticDecay (fun r => f (ρ r)) :=
  not_asymptotic_of_tendsto_ne_zero (hf.tendsto.comp hρ) hf0

-- ============================================================
-- 漸近補正付き汎関数
-- ============================================================

/-- -1/r は正しい漸近減衰を持つ -/
theorem neg_inv_has_asymptotic_decay :
    HasCorrectAsymptoticDecay (fun r => -1 / r) := by
  unfold HasCorrectAsymptoticDecay
  apply (tendsto_const_nhds (x := (-1 : ℝ))).congr'
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [neg_div, mul_neg, mul_div_cancel₀ _ (ne_of_gt hr)]

/-- 漸近補正付きポテンシャル: 局所項 + 長距離 -1/r 補正 -/
def asymptoticCorrectedPotential (v_local : ℝ → ℝ) : ℝ → ℝ :=
  fun r => v_local r - 1 / r

/-- 漸近補正の正しさ:
    局所ポテンシャルが r → ∞ で r * v_local(r) → 0 を満たすならば
    （典型的には指数関数的に減衰する密度から来る局所ポテンシャル）
    補正付きポテンシャルは正しい -1/r 減衰を持つ -/
theorem corrected_has_asymptotic_decay (v_local : ℝ → ℝ)
    (hv : Tendsto (fun r => r * v_local r) atTop (nhds 0)) :
    HasCorrectAsymptoticDecay (asymptoticCorrectedPotential v_local) := by
  unfold HasCorrectAsymptoticDecay asymptoticCorrectedPotential
  -- r * (v_local(r) - 1/r) = r * v_local(r) + (-1)  (for r > 0)
  -- → 0 + (-1) = -1
  have hgoal : Tendsto (fun r => r * v_local r + (-1)) atTop (nhds (-1)) := by
    have := hv.add (tendsto_const_nhds (x := (-1 : ℝ)))
    simp only [zero_add] at this
    exact this
  apply hgoal.congr'
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [mul_sub, mul_one_div_cancel (ne_of_gt hr)]
  ring

/-- 漸近補正は既存の非正性を保存する:
    v_local ≤ 0 ならば v_local - 1/r ≤ 0 (r > 0 で) -/
theorem corrected_nonpositive_of_nonpositive (v_local : ℝ → ℝ)
    (hv : ∀ r, v_local r ≤ 0) (r : ℝ) (hr : 0 < r) :
    asymptoticCorrectedPotential v_local r ≤ 0 := by
  unfold asymptoticCorrectedPotential
  have h1 : 0 < 1 / r := div_pos one_pos hr
  linarith [hv r]

end DFT
