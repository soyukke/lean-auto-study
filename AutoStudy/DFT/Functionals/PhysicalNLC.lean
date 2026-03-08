/-
  物理的に意味のある NonLocalCorrection

  変分関係 v = δE/δρ を持つ非局所補正項。
  E[ρ] = -∫ (ρ(x) - ρ(x+1))² dx
  v[ρ](x) = 2ρ(x-1) - 4ρ(x) + 2ρ(x+1)  （離散ラプラシアン）
-/
import AutoStudy.DFT.FunctionalDerivative
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.Deriv.Pow

open MeasureTheory DFT Filter

noncomputable section

namespace DFT

-- ============================================================
-- 構造体
-- ============================================================

/-- 変分的非局所補正: v = δE/δρ を持つエネルギーベースの補正 -/
structure VariationalNLC where
  E : (ℝ → ℝ) → ℝ
  v : (ℝ → ℝ) → (ℝ → ℝ)
  nonpositive : ∀ ρ, (∀ x, 0 ≤ ρ x) → E ρ ≤ 0
  uniform_vanish : ∀ ρ₀ : ℝ, 0 < ρ₀ → E (fun _ => ρ₀) = 0
  variational : ∀ ρ, HasFunctionalDerivative E ρ (v ρ)

-- ============================================================
-- 定義
-- ============================================================

def shiftDiff (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ρ x - ρ (x + 1)

def shiftDiffEnergy (ρ : ℝ → ℝ) : ℝ := -(∫ x, (shiftDiff ρ x) ^ 2)

def discreteLapV (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * ρ (x - 1) - 4 * ρ x + 2 * ρ (x + 1)

-- ============================================================
-- 非正性
-- ============================================================

theorem shiftDiffEnergy_nonpos (ρ : ℝ → ℝ) : shiftDiffEnergy ρ ≤ 0 := by
  unfold shiftDiffEnergy
  have h : (0 : ℝ) ≤ ∫ x, (shiftDiff ρ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg (shiftDiff ρ x))
  linarith

-- ============================================================
-- 均一密度消失
-- ============================================================

theorem shiftDiffEnergy_const (ρ₀ : ℝ) : shiftDiffEnergy (fun _ => ρ₀) = 0 := by
  unfold shiftDiffEnergy shiftDiff; simp

-- ============================================================
-- 可積分性の仮定
-- ============================================================

structure ShiftIntegrable (ρ η : ℝ → ℝ) : Prop where
  sq : Integrable (fun x => (shiftDiff ρ x) ^ 2)
  cross : Integrable (fun x => shiftDiff ρ x * shiftDiff η x)
  eta_sq : Integrable (fun x => (shiftDiff η x) ^ 2)
  rv : Integrable (fun x => discreteLapV ρ x * η x)
  ρη : Integrable (fun x => ρ x * η x)
  ρη_shift : Integrable (fun x => ρ x * η (x + 1))

-- ============================================================
-- 補助定理
-- ============================================================

theorem shiftDiff_perturb (ρ η : ℝ → ℝ) (ε : ℝ) (x : ℝ) :
    shiftDiff (fun y => ρ y + ε * η y) x = shiftDiff ρ x + ε * shiftDiff η x := by
  unfold shiftDiff; ring

/-- 二次多項式の HasDerivAt -/
theorem hasDerivAt_quadratic (a b c : ℝ) :
    HasDerivAt (fun ε => a + ε * b + ε ^ 2 * c) b 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => ε * b) b 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const b
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * c) 0 0 := by
    have h := (hasDerivAt_pow 2 (0 : ℝ)).mul_const c
    norm_num at h; exact h
  have h3 := ((hasDerivAt_const (0:ℝ) a).add h1).add h2
  have : (0 : ℝ) + b + 0 = b := by ring
  rwa [this] at h3

-- ============================================================
-- 二次展開
-- ============================================================

theorem shiftDiffEnergy_quadratic (ρ η : ℝ → ℝ) (ε : ℝ) (hi : ShiftIntegrable ρ η) :
    shiftDiffEnergy (fun y => ρ y + ε * η y) =
    shiftDiffEnergy ρ + ε * (-2 * ∫ x, shiftDiff ρ x * shiftDiff η x) +
    ε ^ 2 * (-(∫ x, (shiftDiff η x) ^ 2)) := by
  unfold shiftDiffEnergy
  simp only [shiftDiff_perturb]
  -- 被積分関数を展開
  have hexp : (fun x => (shiftDiff ρ x + ε * shiftDiff η x) ^ 2) =
      (fun x => (shiftDiff ρ x) ^ 2 +
        (2 * ε * (shiftDiff ρ x * shiftDiff η x) +
         ε ^ 2 * (shiftDiff η x) ^ 2)) := by
    ext x; ring
  rw [hexp]
  -- 可積分性
  have hi1 := hi.sq
  have hi2 : Integrable (fun x => 2 * ε * (shiftDiff ρ x * shiftDiff η x)) :=
    Integrable.smul (2 * ε) hi.cross
  have hi3 : Integrable (fun x => ε ^ 2 * (shiftDiff η x) ^ 2) :=
    Integrable.smul (ε ^ 2) hi.eta_sq
  -- 積分を分割（have で個別に計算し linarith で結合）
  have hsplit1 : ∫ x, (shiftDiff ρ x) ^ 2 +
      (2 * ε * (shiftDiff ρ x * shiftDiff η x) + ε ^ 2 * (shiftDiff η x) ^ 2) =
      (∫ x, (shiftDiff ρ x) ^ 2) +
      ∫ x, 2 * ε * (shiftDiff ρ x * shiftDiff η x) + ε ^ 2 * (shiftDiff η x) ^ 2 :=
    integral_add hi1 (Integrable.add hi2 hi3)
  have hsplit2 : ∫ x, 2 * ε * (shiftDiff ρ x * shiftDiff η x) +
      ε ^ 2 * (shiftDiff η x) ^ 2 =
      (∫ x, 2 * ε * (shiftDiff ρ x * shiftDiff η x)) +
      ∫ x, ε ^ 2 * (shiftDiff η x) ^ 2 :=
    integral_add hi2 hi3
  have hcm1 : ∫ x, 2 * ε * (shiftDiff ρ x * shiftDiff η x) =
      (2 * ε) * ∫ x, shiftDiff ρ x * shiftDiff η x :=
    integral_const_mul _ _
  have hcm2 : ∫ x, ε ^ 2 * (shiftDiff η x) ^ 2 =
      ε ^ 2 * ∫ x, (shiftDiff η x) ^ 2 :=
    integral_const_mul _ _
  linarith

-- ============================================================
-- 交差項 = 内積（平行移動不変性）
-- ============================================================

theorem cross_eq_innerProduct (ρ η : ℝ → ℝ) (hi : ShiftIntegrable ρ η) :
    -2 * ∫ x, shiftDiff ρ x * shiftDiff η x = innerProduct (discreteLapV ρ) η := by
  -- 戦略: ∫ (rv + 2*cross) = 0 を示し、integral_add で分解して結論
  -- Step 1: ∫ (rv + 2*cross) = 0（被積分関数が h(x+1)-h(x) の形）
  have h_zero : ∫ x, (discreteLapV ρ x * η x +
      (2 : ℝ) * (shiftDiff ρ x * shiftDiff η x)) = 0 := by
    -- 被積分関数を h(x+1) - h(x) に書き換え
    have hpw : ∀ x : ℝ, discreteLapV ρ x * η x +
        (2 : ℝ) * (shiftDiff ρ x * shiftDiff η x) =
        (2 * ρ (x + 1) * η (x + 1) - 2 * ρ x * η (x + 1)) -
        (2 * ρ x * η x - 2 * ρ (x - 1) * η x) := by
      intro x; unfold discreteLapV shiftDiff; ring
    simp_rw [hpw]
    -- h(x) = 2ρ(x)η(x) - 2ρ(x-1)η(x) の可積分性
    have hi_prev : Integrable (fun x => ρ (x - 1) * η x) := by
      have heq : (fun x => ρ (x - 1) * η x) =
          (fun x => (fun t => ρ t * η (t + 1)) (x + (-1))) := by
        ext x
        exact congr_arg₂ (· * ·) (congr_arg ρ (by linarith)) (congr_arg η (by linarith))
      rw [heq]; exact hi.ρη_shift.comp_add_right (-1)
    have hi_h : Integrable (fun x => 2 * ρ x * η x - 2 * ρ (x - 1) * η x) := by
      have heq : (fun x => 2 * ρ x * η x - 2 * ρ (x - 1) * η x) =
          (fun x => (2 : ℝ) * (ρ x * η x) - (2 : ℝ) * (ρ (x - 1) * η x)) := by
        ext x; ring
      rw [heq]; exact Integrable.sub (Integrable.smul (2 : ℝ) hi.ρη)
        (Integrable.smul (2 : ℝ) hi_prev)
    -- h'(x) = 2ρ(x+1)η(x+1) - 2ρ(x)η(x+1) の可積分性
    have hi_shift_ρη : Integrable (fun x => ρ (x + 1) * η (x + 1)) :=
      hi.ρη.comp_add_right 1
    have hi_h' : Integrable (fun x =>
        2 * ρ (x + 1) * η (x + 1) - 2 * ρ x * η (x + 1)) := by
      have heq : (fun x => 2 * ρ (x + 1) * η (x + 1) - 2 * ρ x * η (x + 1)) =
          (fun x => (2 : ℝ) * (ρ (x + 1) * η (x + 1)) -
            (2 : ℝ) * (ρ x * η (x + 1))) := by
        ext x; ring
      rw [heq]; exact Integrable.sub (Integrable.smul (2 : ℝ) hi_shift_ρη)
        (Integrable.smul (2 : ℝ) hi.ρη_shift)
    -- ∫ (h' - h) = ∫ h' - ∫ h = 0 by translation
    rw [integral_sub hi_h' hi_h]
    -- h'(x) = h(x+1) なので ∫ h' = ∫ h
    have key : ∫ x, 2 * ρ (x + 1) * η (x + 1) - 2 * ρ x * η (x + 1) =
        ∫ x, 2 * ρ x * η x - 2 * ρ (x - 1) * η x := by
      have heq : (fun x => 2 * ρ (x + 1) * η (x + 1) - 2 * ρ x * η (x + 1)) =
          (fun x => (fun y => 2 * ρ y * η y - 2 * ρ (y - 1) * η y) (x + 1)) := by
        ext x
        change 2 * ρ (x + 1) * η (x + 1) - 2 * ρ x * η (x + 1) =
            2 * ρ (x + 1) * η (x + 1) - 2 * ρ (x + 1 - 1) * η (x + 1)
        have hx : x + 1 - 1 = x := by ring
        rw [hx]
      rw [heq]; convert integral_add_right_eq_self (μ := volume) _ (1 : ℝ)
    linarith
  -- Step 2: integral_add で分解
  have h_int2 : Integrable (fun x => (2 : ℝ) * (shiftDiff ρ x * shiftDiff η x)) :=
    Integrable.smul (2 : ℝ) hi.cross
  have h_split : ∫ x, (discreteLapV ρ x * η x +
      (2 : ℝ) * (shiftDiff ρ x * shiftDiff η x)) =
      (∫ x, discreteLapV ρ x * η x) +
      (2 : ℝ) * (∫ x, shiftDiff ρ x * shiftDiff η x) := by
    rw [integral_add hi.rv h_int2, integral_const_mul]
  -- Step 3: 結論
  unfold innerProduct
  linarith

-- ============================================================
-- 変分関係
-- ============================================================

theorem shiftDiffEnergy_variational (ρ : ℝ → ℝ)
    (hint : ∀ η, ShiftIntegrable ρ η) :
    HasFunctionalDerivative shiftDiffEnergy ρ (discreteLapV ρ) := by
  intro η
  have hi := hint η
  set b := -2 * ∫ x, shiftDiff ρ x * shiftDiff η x
  set c := -(∫ x, (shiftDiff η x) ^ 2)
  have hpoly : HasDerivAt (fun ε => shiftDiffEnergy ρ + ε * b + ε ^ 2 * c) b 0 :=
    hasDerivAt_quadratic _ _ _
  have hb : b = innerProduct (discreteLapV ρ) η := cross_eq_innerProduct ρ η hi
  rw [hb] at hpoly
  have heq : (fun ε => shiftDiffEnergy (fun y => ρ y + ε * η y)) =ᶠ[nhds 0]
      (fun ε => shiftDiffEnergy ρ + ε * b + ε ^ 2 * c) := by
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    exact ⟨Set.univ, Filter.univ_mem, fun ε _ =>
      shiftDiffEnergy_quadratic ρ η ε hi⟩
  rw [hb] at heq
  exact (heq.hasDerivAt_iff).mpr hpoly

-- ============================================================
-- インスタンス
-- ============================================================

def mkShiftDiffNLC (hint : ∀ ρ η, ShiftIntegrable ρ η) : VariationalNLC where
  E := shiftDiffEnergy
  v := discreteLapV
  nonpositive := fun ρ _ => shiftDiffEnergy_nonpos ρ
  uniform_vanish := fun ρ₀ _ => shiftDiffEnergy_const ρ₀
  variational := fun ρ => shiftDiffEnergy_variational ρ (hint ρ)

end DFT
