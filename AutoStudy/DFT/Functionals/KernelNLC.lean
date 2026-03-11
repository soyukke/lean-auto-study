/-
  カーネル型非局所汎関数の変分理論

  E[ρ] = -∫ ρ(x) (K*ρ)(x) dx   where  (K*ρ)(x) = ∫ K(x-y)ρ(y) dy
  v[ρ](x) = -2(K*ρ)(x)

  非負対称可積分カーネル K（例: Yukawa K(r) = e^{-|r|}）に対して
  v = δE/δρ を Fubini の定理で完全に証明する。
-/
import AutoStudy.DFT.Functionals.PhysicalNLC
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory DFT Filter Function

noncomputable section

namespace DFT

-- ============================================================
-- 定義
-- ============================================================

/-- カーネル畳み込み (K * ρ)(x) = ∫ K(x-y)ρ(y) dy -/
def kernelConv (K ρ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, K (x - y) * ρ y

/-- カーネルエネルギー E[ρ] = -∫ ρ(x)(K*ρ)(x) dx -/
def kernelEnergy (K ρ : ℝ → ℝ) : ℝ := -(∫ x, ρ x * kernelConv K ρ x)

/-- カーネルポテンシャル v[ρ](x) = -2(K*ρ)(x) -/
def kernelV (K ρ : ℝ → ℝ) (x : ℝ) : ℝ := -2 * kernelConv K ρ x

-- ============================================================
-- 可積分性の仮定
-- ============================================================

/-- カーネル汎関数の変分導出に必要な可積分性条件 -/
structure KernelIntegrable (K ρ η : ℝ → ℝ) : Prop where
  inner_ρ : ∀ x, Integrable (fun y => K (x - y) * ρ y)
  inner_η : ∀ x, Integrable (fun y => K (x - y) * η y)
  ρKρ : Integrable (fun x => ρ x * kernelConv K ρ x)
  ηKρ : Integrable (fun x => η x * kernelConv K ρ x)
  ρKη : Integrable (fun x => ρ x * kernelConv K η x)
  ηKη : Integrable (fun x => η x * kernelConv K η x)
  fubini : Integrable (uncurry (fun x y => ρ x * K (x - y) * η y)) (volume.prod volume)

-- ============================================================
-- 畳み込みの摂動展開
-- ============================================================

theorem kernelConv_perturb (K ρ η : ℝ → ℝ) (ε : ℝ) (x : ℝ)
    (hρ : Integrable (fun y => K (x - y) * ρ y))
    (hη : Integrable (fun y => K (x - y) * η y)) :
    kernelConv K (fun y => ρ y + ε * η y) x =
    kernelConv K ρ x + ε * kernelConv K η x := by
  unfold kernelConv
  have hexp : (fun y => K (x - y) * (ρ y + ε * η y)) =
      (fun y => K (x - y) * ρ y + ε * (K (x - y) * η y)) := by
    ext y; ring
  rw [hexp]
  have hη' : Integrable (fun y => ε * (K (x - y) * η y)) := by
    have heq : (fun y => ε * (K (x - y) * η y)) =
        (fun y => ε • (K (x - y) * η y)) := by
      ext y; simp [smul_eq_mul]
    rw [heq]; exact Integrable.smul ε hη
  have h_split := integral_add hρ hη'
  have h_const : ∫ y, ε * (K (x - y) * η y) = ε * ∫ y, K (x - y) * η y :=
    integral_const_mul _ _
  linarith

-- ============================================================
-- 非正性
-- ============================================================

theorem kernelEnergy_nonpos (K ρ : ℝ → ℝ) (hK : ∀ r, 0 ≤ K r) (hρ : ∀ x, 0 ≤ ρ x) :
    kernelEnergy K ρ ≤ 0 := by
  unfold kernelEnergy
  have h : (0 : ℝ) ≤ ∫ x, ρ x * kernelConv K ρ x :=
    integral_nonneg fun x => mul_nonneg (hρ x)
      (integral_nonneg fun y => mul_nonneg (hK _) (hρ y))
  linarith

-- ============================================================
-- 均一密度消失
-- ============================================================

/-- K(x-y) の y に関する積分は平行移動不変 -/
theorem integral_kernel_translate (K : ℝ → ℝ) (hK_symm : ∀ r, K r = K (-r)) (x : ℝ) :
    ∫ y, K (x - y) = ∫ y, K y := by
  have h1 : (fun y => K (x - y)) = (fun y => K (y - x)) := by
    ext y; rw [hK_symm (x - y)]; congr 1; ring
  rw [h1]
  convert integral_sub_right_eq_self (μ := volume) K x

/-- Lebesgue 測度のもとで定数関数の積分は 0（volume ℝ = ∞ のため）。

    注意: この結果は Lean/Mathlib の Lebesgue 測度の取り扱いに依存する。
    volume ℝ = ∞ であるため、定数関数 c ≠ 0 は可積分でなく、
    Bochner 積分の規約により ∫ c = 0 となる。
    物理的には一様密度のエネルギーは有限体積系（周期境界条件など）で
    定義されるべきであり、この結果の直接的な物理的解釈は避けるべきである。 -/
private theorem volume_real_univ_eq_zero : (volume : Measure ℝ).real Set.univ = 0 := by
  simp [Measure.real]

/-- 対称カーネルに対する一様密度のエネルギーが 0 になること。

    注意: この定理は Lean 上の Lebesgue 測度（ℝ 上の volume = ∞）の
    人工的な帰結に依存している。定数関数は無限体積空間で非可積分であり、
    Bochner 積分の規約により ∫ const = 0 として扱われる。
    物理的に意味のある一様密度極限は、有限体積（周期境界条件など）で
    別途定式化する必要がある。 -/
theorem kernelEnergy_const (K : ℝ → ℝ) (hK_symm : ∀ r, K r = K (-r)) (ρ₀ : ℝ) :
    kernelEnergy K (fun _ => ρ₀) = 0 := by
  unfold kernelEnergy kernelConv
  have h_inner : ∀ x, ∫ y, K (x - y) * ρ₀ = ρ₀ * ∫ y, K y := by
    intro x
    have h1 : (fun y => K (x - y) * ρ₀) = (fun y => ρ₀ * K (x - y)) := by ext y; ring
    rw [h1, integral_const_mul, integral_kernel_translate K hK_symm x]
  simp_rw [h_inner]
  rw [integral_const, volume_real_univ_eq_zero, zero_smul, neg_zero]

-- ============================================================
-- 二次展開
-- ============================================================

theorem kernelEnergy_quadratic (K ρ η : ℝ → ℝ) (ε : ℝ) (hi : KernelIntegrable K ρ η) :
    kernelEnergy K (fun y => ρ y + ε * η y) =
    kernelEnergy K ρ +
    ε * (-(∫ x, η x * kernelConv K ρ x + ρ x * kernelConv K η x)) +
    ε ^ 2 * (-(∫ x, η x * kernelConv K η x)) := by
  unfold kernelEnergy
  -- kernelConv の摂動展開を適用
  have hconv : ∀ x, kernelConv K (fun y => ρ y + ε * η y) x =
      kernelConv K ρ x + ε * kernelConv K η x :=
    fun x => kernelConv_perturb K ρ η ε x (hi.inner_ρ x) (hi.inner_η x)
  simp_rw [hconv]
  -- 被積分関数を展開（右結合で integral_add に合わせる）
  have hexp : (fun x => (ρ x + ε * η x) * (kernelConv K ρ x + ε * kernelConv K η x)) =
      (fun x => ρ x * kernelConv K ρ x +
        (ε * (η x * kernelConv K ρ x + ρ x * kernelConv K η x) +
         ε ^ 2 * (η x * kernelConv K η x))) := by
    ext x; ring
  rw [hexp]
  -- 可積分性
  have hi1 := hi.ρKρ
  have hi2 : Integrable (fun x =>
      ε * (η x * kernelConv K ρ x + ρ x * kernelConv K η x)) := by
    have heq : (fun x => ε * (η x * kernelConv K ρ x + ρ x * kernelConv K η x)) =
        (fun x => ε • (η x * kernelConv K ρ x + ρ x * kernelConv K η x)) := by
      ext x; simp [smul_eq_mul]
    rw [heq]; exact Integrable.smul ε (hi.ηKρ.add hi.ρKη)
  have hi3 : Integrable (fun x => ε ^ 2 * (η x * kernelConv K η x)) := by
    have heq : (fun x => ε ^ 2 * (η x * kernelConv K η x)) =
        (fun x => (ε ^ 2) • (η x * kernelConv K η x)) := by
      ext x; simp [smul_eq_mul]
    rw [heq]; exact Integrable.smul (ε ^ 2) hi.ηKη
  -- 積分を分割
  have hsplit1 : ∫ x, ρ x * kernelConv K ρ x +
      (ε * (η x * kernelConv K ρ x + ρ x * kernelConv K η x) +
       ε ^ 2 * (η x * kernelConv K η x)) =
      (∫ x, ρ x * kernelConv K ρ x) +
      ∫ x, ε * (η x * kernelConv K ρ x + ρ x * kernelConv K η x) +
      ε ^ 2 * (η x * kernelConv K η x) :=
    integral_add hi1 (hi2.add hi3)
  have hsplit2 : ∫ x, ε * (η x * kernelConv K ρ x + ρ x * kernelConv K η x) +
      ε ^ 2 * (η x * kernelConv K η x) =
      (∫ x, ε * (η x * kernelConv K ρ x + ρ x * kernelConv K η x)) +
      ∫ x, ε ^ 2 * (η x * kernelConv K η x) :=
    integral_add hi2 hi3
  have hcm1 : ∫ x, ε * (η x * kernelConv K ρ x + ρ x * kernelConv K η x) =
      ε * ∫ x, η x * kernelConv K ρ x + ρ x * kernelConv K η x :=
    integral_const_mul _ _
  have hcm2 : ∫ x, ε ^ 2 * (η x * kernelConv K η x) =
      ε ^ 2 * ∫ x, η x * kernelConv K η x :=
    integral_const_mul _ _
  linarith

-- ============================================================
-- カーネル対称性（Fubini の定理）
-- ============================================================

/-- Fubini の定理による対称性: ∫ ρ·(K*η) = ∫ η·(K*ρ) -/
theorem kernel_cross_symmetry (K ρ η : ℝ → ℝ) (hK_symm : ∀ r, K r = K (-r))
    (hi : KernelIntegrable K ρ η) :
    ∫ x, ρ x * kernelConv K η x = ∫ x, η x * kernelConv K ρ x := by
  -- LHS を ∫ x ∫ y ρ(x)*K(x-y)*η(y) に書き換え
  have h_lhs : (fun x => ρ x * kernelConv K η x) =
      (fun x => ∫ y, ρ x * K (x - y) * η y) := by
    ext x; unfold kernelConv
    rw [← integral_const_mul (ρ x)]
    congr 1; ext y; ring
  -- K 対称性: K(y-x) = K(x-y)
  have h_K_symm : ∀ x y, K (y - x) = K (x - y) := by
    intro x y; rw [hK_symm (y - x)]; congr 1; ring
  -- RHS を ∫ y ∫ x ρ(x)*K(x-y)*η(y) に書き換え
  have h_rhs : (fun y => η y * kernelConv K ρ y) =
      (fun y => ∫ x, ρ x * K (x - y) * η y) := by
    ext y; unfold kernelConv
    rw [← integral_const_mul (η y)]
    congr 1; ext x; rw [h_K_symm]; ring
  rw [h_lhs, h_rhs]
  -- Fubini で積分順序交換
  exact integral_integral_swap hi.fubini

-- ============================================================
-- 交差項 = 内積
-- ============================================================

theorem kernel_cross_eq_innerProduct (K ρ η : ℝ → ℝ) (hK_symm : ∀ r, K r = K (-r))
    (hi : KernelIntegrable K ρ η) :
    -(∫ x, η x * kernelConv K ρ x + ρ x * kernelConv K η x) =
    innerProduct (kernelV K ρ) η := by
  have h_sym := kernel_cross_symmetry K ρ η hK_symm hi
  -- ∫ (η·Kρ + ρ·Kη) = 2 * ∫ η·Kρ
  have h_add : ∫ x, η x * kernelConv K ρ x + ρ x * kernelConv K η x =
      2 * ∫ x, η x * kernelConv K ρ x := by
    rw [integral_add hi.ηKρ hi.ρKη, h_sym]; ring
  rw [h_add]
  -- innerProduct (kernelV K ρ) η = -2 * ∫ η·Kρ
  unfold innerProduct kernelV
  have h1 : ∫ x, -2 * kernelConv K ρ x * η x =
      (-2 : ℝ) * ∫ x, η x * kernelConv K ρ x := by
    rw [show (fun x => -2 * kernelConv K ρ x * η x) =
        (fun x => (-2 : ℝ) * (η x * kernelConv K ρ x)) from by ext x; ring]
    exact integral_const_mul _ _
  linarith

-- ============================================================
-- 変分関係
-- ============================================================

theorem kernelEnergy_variational (K ρ : ℝ → ℝ) (hK_symm : ∀ r, K r = K (-r))
    (hint : ∀ η, KernelIntegrable K ρ η) :
    HasFunctionalDerivative (kernelEnergy K) ρ (kernelV K ρ) := by
  intro η
  have hi := hint η
  set b := -(∫ x, η x * kernelConv K ρ x + ρ x * kernelConv K η x)
  set c := -(∫ x, η x * kernelConv K η x)
  have hpoly : HasDerivAt (fun ε => kernelEnergy K ρ + ε * b + ε ^ 2 * c) b 0 :=
    hasDerivAt_quadratic _ _ _
  have hb : b = innerProduct (kernelV K ρ) η :=
    kernel_cross_eq_innerProduct K ρ η hK_symm hi
  rw [hb] at hpoly
  have heq : (fun ε => kernelEnergy K (fun y => ρ y + ε * η y)) =ᶠ[nhds 0]
      (fun ε => kernelEnergy K ρ + ε * b + ε ^ 2 * c) := by
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    exact ⟨Set.univ, Filter.univ_mem, fun ε _ =>
      kernelEnergy_quadratic K ρ η ε hi⟩
  rw [hb] at heq
  exact (heq.hasDerivAt_iff).mpr hpoly

-- ============================================================
-- VariationalNLC インスタンス
-- ============================================================

/-- カーネル型非局所汎関数の VariationalNLC インスタンス。
    非負対称カーネル K に対して E[ρ] = -∫ ρ(K*ρ), v = -2(K*ρ) で
    変分関係 v = δE/δρ が成立する。 -/
def mkKernelNLC (K : ℝ → ℝ)
    (hK_nonneg : ∀ r, 0 ≤ K r)
    (hK_symm : ∀ r, K r = K (-r))
    (hint : ∀ ρ η, KernelIntegrable K ρ η) : VariationalNLC where
  E := kernelEnergy K
  v := kernelV K
  nonpositive := fun ρ hρ => kernelEnergy_nonpos K ρ hK_nonneg hρ
  uniform_vanish := fun ρ₀ _ => kernelEnergy_const K hK_symm ρ₀
  variational := fun ρ => kernelEnergy_variational K ρ hK_symm (hint ρ)

end DFT
