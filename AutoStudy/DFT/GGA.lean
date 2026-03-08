/-
  一般化勾配近似 (GGA)

  LDA を密度の勾配情報で拡張した近似:
    E_xc^GGA[ρ] = ∫ f(ρ(x), |∇ρ(x)|) dx

  交換エネルギーの場合、enhancement factor F_x(s) を導入:
    E_x^GGA[ρ] = ∫ ρ(x) · ε_x^LDA(ρ(x)) · F_x(s(x)) dx
    s = |∇ρ| / (2 k_F ρ) は無次元化された勾配

  GGA は LDA より多くの厳密条件を満たすことができる。
  PBE (Perdew-Burke-Ernzerhof) が代表的な GGA 汎関数。
-/
import AutoStudy.DFT.ExchangeCorrelation
import AutoStudy.DFT.ExactConstraints
import AutoStudy.DFT.LDA

open MeasureTheory DFT

noncomputable section

namespace DFT

/-- GGA 交換エネルギー:
    E_x^GGA[ρ, ∇ρ] = ∫ ρ(x) · ε_x(ρ(x)) · F_x(ρ(x), |∇ρ(x)|) dx

    ε_x: LDA 交換エネルギー密度
    F_x: enhancement factor（≥ 0 であり、∇ρ = 0 で F_x = 1 に戻る） -/
def ggaExchangeEnergy (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ) (ρ gradρ : ℝ → ℝ) : ℝ :=
  ∫ x, ρ x * ε_x (ρ x) * F_x (ρ x) (gradρ x)

/-- GGA 相関エネルギー:
    E_c^GGA[ρ, ∇ρ] = ∫ ρ(x) · (ε_c(ρ(x)) + H(ρ(x), |∇ρ(x)|)) dx

    H: 勾配補正項 -/
def ggaCorrelationEnergy (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (ρ gradρ : ℝ → ℝ) : ℝ :=
  ∫ x, ρ x * (ε_c (ρ x) + H (ρ x) (gradρ x))

/-- GGA を XCFunctional として構成する（勾配を固定した場合） -/
def mkGGAFunctional (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ)
    (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (gradρ : ℝ → ℝ) : XCFunctional where
  E_xc := fun ρ => ggaExchangeEnergy ε_x F_x ρ gradρ + ggaCorrelationEnergy ε_c H ρ gradρ
  E_x := fun ρ => ggaExchangeEnergy ε_x F_x ρ gradρ
  E_c := fun ρ => ggaCorrelationEnergy ε_c H ρ gradρ
  decomposition := fun _ => rfl

/-- GGA は均一密度極限で LDA に帰着する:
    ∇ρ = 0 のとき F_x(ρ, 0) = 1 ならば
    E_x^GGA = E_x^LDA -/
theorem gga_reduces_to_lda_exchange (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ)
    (hF_unit : ∀ r, F_x r 0 = 1) (ρ : ℝ → ℝ) :
    ggaExchangeEnergy ε_x F_x ρ (fun _ => 0) = ldaExchangeEnergy ε_x ρ := by
  unfold ggaExchangeEnergy ldaExchangeEnergy
  congr 1
  ext x
  rw [hF_unit (ρ x), mul_one]

/-- GGA 交換エネルギーの非正性:
    ε_x(ρ) ≤ 0 かつ F_x(ρ, g) ≥ 0 ならば E_x^GGA ≤ 0 -/
theorem gga_exchange_nonpositive (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ)
    (hε : ∀ r, 0 ≤ r → ε_x r ≤ 0)
    (hF : ∀ r g, 0 ≤ F_x r g)
    (gradρ : ℝ → ℝ) :
    IsExchangeNonPositive (fun ρ => ggaExchangeEnergy ε_x F_x ρ gradρ) := by
  intro ρ hρ
  unfold ggaExchangeEnergy
  apply integral_nonpos
  intro x
  -- ρ(x) ≥ 0, ε_x(ρ(x)) ≤ 0, F_x(ρ(x), gradρ(x)) ≥ 0
  -- なので ρ(x) · ε_x(ρ(x)) · F_x(...) ≤ 0
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonneg_of_nonpos (hρ x) (hε (ρ x) (hρ x))
  · exact hF (ρ x) (gradρ x)

/-- GGA 相関エネルギーの非正性:
    ε_c(ρ) + H(ρ, g) ≤ 0（非負密度に対して）ならば E_c^GGA ≤ 0 -/
theorem gga_correlation_nonpositive (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (hεH : ∀ r g, 0 ≤ r → ε_c r + H r g ≤ 0)
    (gradρ : ℝ → ℝ) :
    IsCorrelationNonPositive (fun ρ => ggaCorrelationEnergy ε_c H ρ gradρ) := by
  intro ρ hρ
  unfold ggaCorrelationEnergy
  apply integral_nonpos
  intro x
  exact mul_nonpos_of_nonneg_of_nonpos (hρ x) (hεH (ρ x) (gradρ x) (hρ x))

/-- Enhancement factor の物理的制約:
    F_x は Lieb-Oxford 限界と整合的でなければならない -/
def EnhancementFactorBounded (F_x : ℝ → ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ r g, F_x r g ≤ C

/-- Enhancement factor が有界ならば GGA は LDA 比で有界 -/
theorem gga_bounded_by_lda (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ) (C : ℝ)
    (hF_bound : EnhancementFactorBounded F_x C)
    (hε_nonpos : ∀ r, 0 ≤ r → ε_x r ≤ 0)
    (ρ : ℝ → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (gradρ : ℝ → ℝ)
    (hint_gga : Integrable (fun x => ρ x * ε_x (ρ x) * F_x (ρ x) (gradρ x)))
    (hint_lda : Integrable (fun x => C * (ρ x * ε_x (ρ x)))) :
    C * ldaExchangeEnergy ε_x ρ ≤ ggaExchangeEnergy ε_x F_x ρ gradρ := by
  unfold ggaExchangeEnergy ldaExchangeEnergy
  rw [← integral_const_mul]
  apply integral_mono hint_lda hint_gga
  intro x
  -- C * (ρ · ε_x) ≤ ρ · ε_x · F_x
  -- ρ · ε_x ≤ 0 かつ F_x ≤ C なので nonpos_right で示す
  change C * (ρ x * ε_x (ρ x)) ≤ ρ x * ε_x (ρ x) * F_x (ρ x) (gradρ x)
  have hρε : ρ x * ε_x (ρ x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hρ x) (hε_nonpos (ρ x) (hρ x))
  calc C * (ρ x * ε_x (ρ x))
      _ ≤ F_x (ρ x) (gradρ x) * (ρ x * ε_x (ρ x)) :=
          mul_le_mul_of_nonpos_right (hF_bound (ρ x) (gradρ x)) hρε
      _ = ρ x * ε_x (ρ x) * F_x (ρ x) (gradρ x) := by ring

end DFT
