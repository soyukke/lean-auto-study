/-
  LB94 (van Leeuwen-Baerends, 1994) モデルポテンシャル

  GGA 交換ポテンシャルに漸近補正を加え、正しい -1/r 減衰を実現する。
  エネルギー汎関数ではなくポテンシャルを直接定義するモデルポテンシャル。

  定義:
    v_x^LB94(r) = v_x^LDA(ρ(r)) + Δv^LB(ρ(r), |∇ρ(r)|)
    Δv^LB = - β ρ^{1/3} x² / (1 + 3β x arsinh(x))
    x = |∇ρ| / ρ^{4/3}  (換算密度勾配)

  性質:
    - 均一密度極限 (x=0): LDA に帰着 (Δv^LB = 0)
    - r → ∞: -1/r 漸近減衰（指数減衰する密度に対して）
    - エネルギー汎関数が存在しない（モデルポテンシャル固有の問題）

  参考文献:
    van Leeuwen & Baerends, Phys. Rev. A 49, 2421 (1994)
-/
import AutoStudy.DFT.ModelPotential
import AutoStudy.DFT.LDA
import Mathlib.Analysis.SpecialFunctions.Arsinh

open MeasureTheory DFT Filter Real

noncomputable section

namespace DFT

-- ============================================================
-- LB94 の構成要素
-- ============================================================

/-- LB94 補正項の分母: 1 + 3β x arsinh(x) -/
def lb94Denom (β x : ℝ) : ℝ :=
  1 + 3 * β * x * arsinh x

/-- LB94 補正項（換算密度勾配 x とキュービックルート ρ_cbrt = ρ^{1/3} を入力）:
    Δv^LB = - β · ρ_cbrt · x² / (1 + 3β x arsinh(x))

    ρ_cbrt と x は外部で計算される。
    これにより rpow の型解決問題を回避しつつ、
    代数的性質の証明に集中できる。 -/
def lb94Correction (β ρ_cbrt x : ℝ) : ℝ :=
  -β * ρ_cbrt * x ^ 2 / lb94Denom β x

/-- 物理的な LB94 ポテンシャル:
    v^LB94(r) = v_LDA(ρ(r)) + Δv^LB(ρ_cbrt(r), x(r))

    ρ_cbrt: r ↦ ρ(r)^{1/3} (キュービックルート)
    redGrad: r ↦ |∇ρ(r)| / ρ(r)^{4/3} (換算密度勾配) -/
def lb94Potential (v_LDA : ℝ → ℝ) (β : ℝ)
    (ρ_cbrt : ℝ → ℝ) (redGrad : ℝ → ℝ) : ℝ → ℝ :=
  fun r => v_LDA r + lb94Correction β (ρ_cbrt r) (redGrad r)

/-- ModelPotential としての LB94。
    密度から ρ_cbrt と redGrad を計算する関数を受け取る。 -/
def lb94AsModelPotential (v_LDA_fn : ℝ → ℝ) (β : ℝ)
    (cbrt_fn : (ℝ → ℝ) → (ℝ → ℝ))
    (redGrad_fn : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)) : ModelPotential where
  v_xc := fun ρ gradρ => fun r =>
    v_LDA_fn (ρ r) + lb94Correction β (cbrt_fn ρ r) (redGrad_fn ρ gradρ r)

-- ============================================================
-- 補助定理
-- ============================================================

/-- x = 0 のとき LB94 補正は 0 -/
theorem lb94Correction_zero_x (β ρ_cbrt : ℝ) :
    lb94Correction β ρ_cbrt 0 = 0 := by
  unfold lb94Correction lb94Denom
  simp [arsinh_zero]

/-- β = 0 のとき LB94 補正は 0 -/
theorem lb94Correction_zero_beta (ρ_cbrt x : ℝ) :
    lb94Correction 0 ρ_cbrt x = 0 := by
  unfold lb94Correction
  simp

/-- LB94 分母の正値性:
    β > 0, x ≥ 0 ならば 1 + 3β x arsinh(x) > 0 -/
theorem lb94Denom_pos (β x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    0 < lb94Denom β x := by
  unfold lb94Denom
  have hax : 0 ≤ arsinh x := arsinh_nonneg_iff.mpr hx
  have h : 0 ≤ 3 * β * x * arsinh x := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · linarith
        · exact le_of_lt hβ
      · exact hx
    · exact hax
  linarith

/-- LB94 補正項の非正性:
    β > 0, ρ_cbrt ≥ 0, x ≥ 0 ならば Δv^LB ≤ 0 -/
theorem lb94Correction_nonpos (β ρ_cbrt x : ℝ)
    (hβ : 0 < β) (hρ : 0 ≤ ρ_cbrt) (hx : 0 ≤ x) :
    lb94Correction β ρ_cbrt x ≤ 0 := by
  unfold lb94Correction
  apply div_nonpos_of_nonpos_of_nonneg
  · -- -β * ρ_cbrt * x ^ 2 = -(β * ρ_cbrt * x ^ 2) ≤ 0
    have h : 0 ≤ β * ρ_cbrt * x ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt hβ) hρ) (sq_nonneg _)
    linarith
  · exact le_of_lt (lb94Denom_pos β x hβ hx)

-- ============================================================
-- 条件1: 均一密度極限での LDA 帰着
-- ============================================================

/-- 均一密度 (∇ρ = 0) では換算密度勾配 x = 0 なので LB94 補正は消える -/
theorem lb94_reduces_to_lda_at_uniform (v_LDA : ℝ → ℝ) (β : ℝ) (ρ_cbrt : ℝ → ℝ) :
    lb94Potential v_LDA β ρ_cbrt (fun _ => 0) = v_LDA := by
  ext r
  simp [lb94Potential, lb94Correction_zero_x]

/-- ModelPotential 版: ∇ρ = 0 で局所ポテンシャルに帰着 -/
theorem lb94_model_reduces_to_local (v_LDA_fn : ℝ → ℝ) (β : ℝ)
    (cbrt_fn : (ℝ → ℝ) → (ℝ → ℝ))
    (redGrad_fn : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ))
    (hred_zero : ∀ ρ r, redGrad_fn ρ (fun _ => 0) r = 0) :
    (lb94AsModelPotential v_LDA_fn β cbrt_fn redGrad_fn).ReducesToLocal v_LDA_fn := by
  intro ρ
  ext r
  simp [lb94AsModelPotential, hred_zero, lb94Correction_zero_x]

-- ============================================================
-- 条件2: 漸近減衰（仮定付き版）
-- ============================================================

/-- LB94 の漸近減衰:
    LDA ポテンシャル部分が r * v_LDA(r) → 0 を満たし、
    LB94 補正項が r * Δv^LB(r) → -1 を満たすならば、
    全体として正しい -1/r 漸近減衰を持つ。 -/
theorem lb94_asymptotic_decay (v_LDA : ℝ → ℝ) (β : ℝ)
    (ρ_cbrt redGrad : ℝ → ℝ)
    (hv_local : Tendsto (fun r => r * v_LDA r) atTop (nhds 0))
    (hcorr : Tendsto (fun r => r * lb94Correction β (ρ_cbrt r) (redGrad r))
      atTop (nhds (-1))) :
    HasCorrectAsymptoticDecay (lb94Potential v_LDA β ρ_cbrt redGrad) := by
  unfold HasCorrectAsymptoticDecay lb94Potential
  have hgoal : Tendsto
    (fun r => r * v_LDA r + r * lb94Correction β (ρ_cbrt r) (redGrad r))
    atTop (nhds (-1)) := by
    have := hv_local.add hcorr
    simp only [zero_add] at this
    exact this
  apply hgoal.congr'
  filter_upwards with r
  ring

-- ============================================================
-- LB94 の限界
-- ============================================================

-- LB94 はモデルポテンシャルであり、一般にはエネルギー汎関数が存在しない。
-- 全エネルギー計算や変分的最適化には使えない。
-- 物理的には v_xc が汎関数微分として表現できないことに対応する。

-- ============================================================
-- 条件充足の比較
-- ============================================================

/-- LB94 の条件充足まとめ（ポテンシャルレベル）:
    - 均一密度極限:   ✅ (lb94_reduces_to_lda_at_uniform)
    - 漸近減衰:       ✅ (lb94_asymptotic_decay, 仮定付き)
    - 補正項の非正性: ✅ (lb94Correction_nonpos)
    - エネルギー汎関数: ❌ (存在しない)
    - Lieb-Oxford:    N/A (エネルギー汎関数が不在)
    - サイズ整合性:   N/A (エネルギー汎関数が不在) -/
theorem lb94_properties (β : ℝ) (hβ : 0 < β) :
    -- 1. 補正項の非正性
    (∀ ρ_cbrt x, 0 ≤ ρ_cbrt → 0 ≤ x → lb94Correction β ρ_cbrt x ≤ 0) ∧
    -- 2. x = 0 で補正消失
    (∀ ρ_cbrt, lb94Correction β ρ_cbrt 0 = 0) ∧
    -- 3. 分母の正値性
    (∀ x, 0 ≤ x → 0 < lb94Denom β x) :=
  ⟨fun ρ x hρ hx => lb94Correction_nonpos β ρ x hβ hρ hx,
   fun ρ => lb94Correction_zero_x β ρ,
   fun x hx => lb94Denom_pos β x hβ hx⟩

end DFT
