/-
  LB94 漸近挙動の完全証明

  指数減衰密度 ρ(r) = C exp(-αr) に対して、LB94 補正項が
  r * Δv^LB(r) → -1 (r → ∞) を満たすことを証明する。
-/
import AutoStudy.DFT.Functionals.LB94
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory DFT Filter Real Topology

noncomputable section

namespace DFT

-- ============================================================
-- Part 1: arsinh の上下界
-- ============================================================

theorem sqrt_one_add_sq_ge {y : ℝ} (hy : 0 ≤ y) :
    y ≤ sqrt (1 + y ^ 2) := by
  calc y = sqrt (y ^ 2) := (sqrt_sq hy).symm
    _ ≤ sqrt (1 + y ^ 2) := sqrt_le_sqrt (by linarith)

theorem sqrt_one_add_sq_le {y : ℝ} (hy : 0 ≤ y) :
    sqrt (1 + y ^ 2) ≤ y + 1 := by
  rw [sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg y]

/-- arsinh の下界: y > 0 のとき log(2y) ≤ arsinh(y) -/
theorem arsinh_ge_log_two_mul {y : ℝ} (hy : 0 < y) :
    log (2 * y) ≤ arsinh y := by
  unfold arsinh
  exact log_le_log (by positivity) (by linarith [sqrt_one_add_sq_ge (le_of_lt hy)])

/-- arsinh の上界: y ≥ 0 のとき arsinh(y) ≤ log(2y+1) -/
theorem arsinh_le_log_two_mul_add_one {y : ℝ} (hy : 0 ≤ y) :
    arsinh y ≤ log (2 * y + 1) := by
  unfold arsinh
  apply log_le_log
  · positivity [sqrt_nonneg]
  · linarith [sqrt_one_add_sq_le hy]

-- ============================================================
-- Part 2: 基本極限
-- ============================================================

/-- a > 0 のとき -a·r / (a·r + c) → -1 -/
theorem tendsto_neg_ratio {a c : ℝ} (ha : 0 < a) :
    Tendsto (fun r => -a * r / (a * r + c)) atTop (nhds (-1)) := by
  have htop : Tendsto (fun r => a * r + c) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop c
      (Filter.Tendsto.const_mul_atTop ha tendsto_id)
  suffices h : Tendsto (fun r => -1 + c / (a * r + c)) atTop (nhds (-1)) by
    apply h.congr'
    filter_upwards [htop.eventually (eventually_gt_atTop 0)] with r hr
    have hne : a * r + c ≠ 0 := ne_of_gt hr
    field_simp [hne]; ring
  have hrem : Tendsto (fun r => c / (a * r + c)) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds htop
  have goal : Tendsto (fun r => -1 + c / (a * r + c)) atTop (nhds (-1 + 0)) :=
    tendsto_const_nhds.add hrem
  simp only [add_zero] at goal; exact goal

/-- a > 0 のとき a·r / (a·r + c) → 1 -/
theorem tendsto_pos_ratio {a c : ℝ} (ha : 0 < a) :
    Tendsto (fun r => a * r / (a * r + c)) atTop (nhds 1) := by
  have h := (tendsto_neg_ratio ha (c := c)).neg
  simp only [neg_neg] at h
  apply h.congr'
  filter_upwards with r
  simp [neg_mul, neg_div, neg_neg]

-- ============================================================
-- Part 3: 指数減衰密度モデル
-- ============================================================

/-- 指数減衰密度モデル:
    ρ_cbrt(r) = A exp(-γr), redGrad(r) = B exp(γr)。
    物理: ρ = C exp(-αr) のとき A = C^{1/3}, B = α/C^{1/3}, γ = α/3。 -/
structure ExpDecayModel where
  A : ℝ
  B : ℝ
  γ : ℝ
  hA : 0 < A
  hB : 0 < B
  hγ : 0 < γ
  /-- 物理的整合性: A·B = 3γ -/
  consistency : A * B = 3 * γ

def ExpDecayModel.ρ_cbrt (m : ExpDecayModel) (r : ℝ) : ℝ :=
  m.A * exp (-m.γ * r)

def ExpDecayModel.redGrad (m : ExpDecayModel) (r : ℝ) : ℝ :=
  m.B * exp (m.γ * r)

theorem ExpDecayModel.ρ_cbrt_pos (m : ExpDecayModel) (r : ℝ) :
    0 < m.ρ_cbrt r := mul_pos m.hA (exp_pos _)

theorem ExpDecayModel.redGrad_pos (m : ExpDecayModel) (r : ℝ) :
    0 < m.redGrad r := mul_pos m.hB (exp_pos _)

/-- ρ_cbrt * redGrad = AB (exp が相殺して定数) -/
theorem ExpDecayModel.cbrt_mul_redGrad (m : ExpDecayModel) (r : ℝ) :
    m.ρ_cbrt r * m.redGrad r = m.A * m.B := by
  simp only [ExpDecayModel.ρ_cbrt, ExpDecayModel.redGrad]
  rw [show m.A * exp (-m.γ * r) * (m.B * exp (m.γ * r)) =
      m.A * m.B * (exp (-m.γ * r) * exp (m.γ * r)) from by ring,
    ← exp_add, show -m.γ * r + m.γ * r = 0 from by ring, exp_zero, mul_one]

/-- ρ_cbrt * redGrad² = AB² exp(γr) -/
theorem ExpDecayModel.cbrt_mul_sq (m : ExpDecayModel) (r : ℝ) :
    m.ρ_cbrt r * (m.redGrad r) ^ 2 = m.A * m.B ^ 2 * exp (m.γ * r) := by
  simp only [ExpDecayModel.ρ_cbrt, ExpDecayModel.redGrad, sq]
  rw [show m.A * exp (-m.γ * r) * (m.B * exp (m.γ * r) * (m.B * exp (m.γ * r))) =
      m.A * (m.B * m.B) * (exp (-m.γ * r) * exp (m.γ * r) * exp (m.γ * r)) from by ring,
    ← exp_add, show -m.γ * r + m.γ * r = 0 from by ring, exp_zero, one_mul]

/-- redGrad → +∞ -/
theorem ExpDecayModel.redGrad_tendsto (m : ExpDecayModel) :
    Tendsto m.redGrad atTop atTop := by
  apply Filter.Tendsto.const_mul_atTop m.hB
  exact tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop m.hγ tendsto_id)

-- ============================================================
-- Part 4: γr / arsinh(B exp(γr)) → 1
-- ============================================================

private theorem log_two_redGrad (m : ExpDecayModel) (r : ℝ) :
    log (2 * m.redGrad r) = log (2 * m.B) + m.γ * r := by
  unfold ExpDecayModel.redGrad
  rw [show 2 * (m.B * exp (m.γ * r)) = (2 * m.B) * exp (m.γ * r) from by ring,
    log_mul (ne_of_gt (mul_pos two_pos m.hB)) (ne_of_gt (exp_pos _)), log_exp]

private theorem log_four_redGrad (m : ExpDecayModel) (r : ℝ) :
    log (4 * m.redGrad r) = log (4 * m.B) + m.γ * r := by
  unfold ExpDecayModel.redGrad
  rw [show 4 * (m.B * exp (m.γ * r)) = (4 * m.B) * exp (m.γ * r) from by ring,
    log_mul (ne_of_gt (mul_pos (by norm_num : (0:ℝ) < 4) m.hB))
      (ne_of_gt (exp_pos _)), log_exp]

/-- arsinh → +∞ -/
theorem tendsto_arsinh_atTop : Tendsto arsinh atTop atTop :=
  sinhOrderIso.symm.tendsto_atTop

/-- γr / arsinh(B exp(γr)) → 1 -/
theorem gamma_r_div_arsinh_tendsto (m : ExpDecayModel) :
    Tendsto (fun r => m.γ * r / arsinh (m.redGrad r)) atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
  -- 下界: γr/(log(4B)+γr) → 1
  · exact tendsto_pos_ratio m.hγ (c := log (4 * m.B))
  -- 上界: γr/(log(2B)+γr) → 1
  · exact tendsto_pos_ratio m.hγ (c := log (2 * m.B))
  -- 下界 ≤ γr/arsinh(x): arsinh ≤ log(4x) = log(4B)+γr → γr/(log(4B)+γr) ≤ γr/arsinh
  · filter_upwards [m.redGrad_tendsto.eventually (eventually_ge_atTop 1),
                     eventually_gt_atTop 0] with r hx1 hr
    have hγr_pos : 0 < m.γ * r := mul_pos m.hγ hr
    have hx_pos : 0 < m.redGrad r := m.redGrad_pos r
    have harsinh_pos : 0 < arsinh (m.redGrad r) := arsinh_pos_iff.mpr hx_pos
    have h_arsinh_le : arsinh (m.redGrad r) ≤ m.γ * r + log (4 * m.B) := by
      calc arsinh (m.redGrad r)
          ≤ log (2 * m.redGrad r + 1) :=
            arsinh_le_log_two_mul_add_one (le_of_lt hx_pos)
        _ ≤ log (4 * m.redGrad r) := by
            apply log_le_log (by positivity); linarith
        _ = log (4 * m.B) + m.γ * r := log_four_redGrad m r
        _ = m.γ * r + log (4 * m.B) := add_comm _ _
    exact div_le_div_of_nonneg_left (le_of_lt hγr_pos) harsinh_pos h_arsinh_le
  -- γr/arsinh ≤ γr/(log(2B)+γr): arsinh ≥ log(2x) = log(2B)+γr
  · filter_upwards [m.redGrad_tendsto.eventually (eventually_ge_atTop 1),
                     eventually_gt_atTop 0] with r hx1 hr
    have hγr_pos : 0 < m.γ * r := mul_pos m.hγ hr
    have h_arsinh_ge : m.γ * r + log (2 * m.B) ≤ arsinh (m.redGrad r) := by
      rw [show m.γ * r + log (2 * m.B) = log (2 * m.B) + m.γ * r from add_comm _ _,
        ← log_two_redGrad m r]
      exact arsinh_ge_log_two_mul (m.redGrad_pos r)
    have hlog_pos : 0 < m.γ * r + log (2 * m.B) := by
      rw [show m.γ * r + log (2 * m.B) = log (2 * m.B) + m.γ * r from add_comm _ _,
        ← log_two_redGrad m r]
      exact log_pos (by linarith)
    exact div_le_div_of_nonneg_left (le_of_lt hγr_pos) hlog_pos h_arsinh_ge

-- ============================================================
-- Part 5: factor1 → -1
-- ============================================================

/-- factor1 = -(AB)·r / (3·arsinh(redGrad r)) → -1 -/
theorem factor1_tendsto (m : ExpDecayModel) :
    Tendsto (fun r => -(m.A * m.B) * r / (3 * arsinh (m.redGrad r)))
      atTop (nhds (-1)) := by
  have h_inv := gamma_r_div_arsinh_tendsto m
  have hAB : m.A * m.B = 3 * m.γ := m.consistency
  -- -(3γ)r/(3·arsinh) = -(γr/arsinh) → -1
  have h_neg : Tendsto (fun r => -(m.γ * r / arsinh (m.redGrad r))) atTop (nhds (-1)) :=
    h_inv.neg
  apply h_neg.congr'
  filter_upwards [m.redGrad_tendsto.eventually (eventually_gt_atTop 0)] with r hxr
  have harsinh_ne : arsinh (m.redGrad r) ≠ 0 := ne_of_gt (arsinh_pos_iff.mpr hxr)
  rw [hAB]; field_simp [harsinh_ne]

-- ============================================================
-- Part 6: factor2 → 1
-- ============================================================

/-- factor2 = 3·β·x·arsinh(x) / lb94Denom β x → 1 -/
theorem factor2_tendsto (m : ExpDecayModel) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun r => 3 * β * m.redGrad r * arsinh (m.redGrad r) /
      lb94Denom β (m.redGrad r)) atTop (nhds 1) := by
  suffices hs : Tendsto (fun r => 1 - 1 / (1 + 3 * β * m.redGrad r * arsinh (m.redGrad r)))
      atTop (nhds 1) by
    apply hs.congr'
    filter_upwards [m.redGrad_tendsto.eventually (eventually_gt_atTop 0)] with r hxr
    have harsinh_pos : 0 < arsinh (m.redGrad r) := arsinh_pos_iff.mpr hxr
    have h1d_ne : 1 + 3 * β * m.redGrad r * arsinh (m.redGrad r) ≠ 0 := by positivity
    unfold lb94Denom; field_simp [h1d_ne]; ring
  -- 1 + d → ∞ where d = 3β·x·arsinh(x)
  have hd_tendsto : Tendsto (fun r => 1 + 3 * β * m.redGrad r * arsinh (m.redGrad r))
      atTop atTop := by
    apply Filter.tendsto_atTop_add_const_left atTop 1
    -- x·arsinh(x) → ∞
    have hxa : Tendsto (fun r => m.redGrad r * arsinh (m.redGrad r)) atTop atTop :=
      m.redGrad_tendsto.atTop_mul_atTop₀
        (tendsto_arsinh_atTop.comp m.redGrad_tendsto)
    -- 3β · (x·arsinh(x))  - need to handle associativity
    have h3β : (0 : ℝ) < 3 * β := by positivity
    apply (Filter.Tendsto.const_mul_atTop h3β hxa).congr'
    filter_upwards with r; ring
  have h_inv : Tendsto (fun r => 1 / (1 + 3 * β * m.redGrad r * arsinh (m.redGrad r)))
      atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hd_tendsto
  have h_sub : Tendsto (fun r => 1 - 1 / (1 + 3 * β * m.redGrad r * arsinh (m.redGrad r)))
      atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub h_inv
  rwa [sub_zero] at h_sub

-- ============================================================
-- Part 7: 核心定理
-- ============================================================

/-- 核心定理: 指数減衰密度に対する LB94 の -1/r 漸近減衰 -/
theorem lb94_exp_decay_asymptotic (m : ExpDecayModel) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun r => r * lb94Correction β (m.ρ_cbrt r) (m.redGrad r))
      atTop (nhds (-1)) := by
  have hf1 := factor1_tendsto m
  have hf2 := factor2_tendsto m β hβ
  have hprod : Tendsto (fun r =>
      (-(m.A * m.B) * r / (3 * arsinh (m.redGrad r))) *
      (3 * β * m.redGrad r * arsinh (m.redGrad r) / lb94Denom β (m.redGrad r)))
      atTop (nhds ((-1) * 1)) :=
    hf1.mul hf2
  simp only [mul_one] at hprod
  apply hprod.congr'
  filter_upwards [m.redGrad_tendsto.eventually (eventually_gt_atTop 0)] with r hxr
  have harsinh_ne : arsinh (m.redGrad r) ≠ 0 :=
    ne_of_gt (arsinh_pos_iff.mpr hxr)
  have hdenom_ne : lb94Denom β (m.redGrad r) ≠ 0 :=
    ne_of_gt (lb94Denom_pos β (m.redGrad r) hβ (le_of_lt hxr))
  -- ρ_cbrt, redGrad を展開
  simp only [lb94Correction, lb94Denom, ExpDecayModel.ρ_cbrt, ExpDecayModel.redGrad]
  have hexp_ne : exp (m.γ * r) ≠ 0 := ne_of_gt (exp_pos _)
  have hB_ne : m.B ≠ 0 := ne_of_gt m.hB
  have hA_ne : m.A ≠ 0 := ne_of_gt m.hA
  -- r * exp(γr) * exp(-γr) = r を使って簡約
  have hcancel : r * exp (m.γ * r) * exp (-(m.γ * r)) = r := by
    rw [mul_assoc, ← exp_add]; simp
  -- 展開後のゴールに hcancel を適用するため conv で処理
  -- ゴールは factor1*factor2 = r * (-β * (A * exp(-γr)) * (B * exp(γr))^2 / denom)
  -- RHS を簡約: A * exp(-γr) * (B * exp(γr))^2 = A * B^2 * exp(γr)
  -- 直接 calc で:
  -- exp(-γr) * exp(γr) = 1 で相殺
  have h_exp_cancel : exp (-m.γ * r) * exp (m.γ * r) = 1 := by
    rw [← exp_add]; simp [neg_add_cancel]
  -- RHS の A * exp(-γr) * (B * exp(γr))^2 を書き換え
  -- = A * B^2 * exp(-γr) * exp(γr)^2 = A * B^2 * exp(γr)
  -- ゴールの RHS で conv を使って簡約
  conv_rhs =>
    rw [show -β * (m.A * exp (-m.γ * r)) * (m.B * exp (m.γ * r)) ^ 2 =
        -β * m.A * m.B ^ 2 * (exp (-m.γ * r) * exp (m.γ * r)) * exp (m.γ * r) from by ring]
    rw [h_exp_cancel]
    ring_nf
  -- conv_rhs で ring_nf した後の残りを field_simp で処理
  field_simp [harsinh_ne, hdenom_ne, hB_ne, hA_ne, ne_of_gt (exp_pos (m.γ * r))]

/-- 完全な漸近定理: LB94 ポテンシャルの -1/r 減衰 -/
theorem lb94_full_asymptotic (v_LDA : ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (m : ExpDecayModel)
    (hv_LDA : Tendsto (fun r => r * v_LDA r) atTop (nhds 0)) :
    HasCorrectAsymptoticDecay (lb94Potential v_LDA β m.ρ_cbrt m.redGrad) :=
  lb94_asymptotic_decay v_LDA β m.ρ_cbrt m.redGrad hv_LDA
    (lb94_exp_decay_asymptotic m β hβ)

end DFT
