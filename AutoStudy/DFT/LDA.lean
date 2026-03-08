/-
  局所密度近似 (LDA)

  DFT の最も基本的な近似: 交換相関エネルギーを密度の局所関数で表す。
    E_xc^LDA[ρ] = ∫ ρ(x) · ε_xc(ρ(x)) dx

  ここで ε_xc(ρ) は一様電子ガスのエネルギー密度。
  3次元の場合:
    ε_x(ρ) = -C_x · ρ^{1/3}  (Dirac 交換)
    ε_c(ρ) = 数値的にフィットされた関数 (VWN, PZ81 等)

  証明する性質:
    - E_xc = E_x + E_c の分解（構造的に保証）
    - 交換エネルギーの非正性
    - 均一密度極限での正しさ（定義より自明）
-/
import AutoStudy.DFT.ExchangeCorrelation
import AutoStudy.DFT.ExactConstraints

open MeasureTheory DFT

noncomputable section

namespace DFT

/-- LDA 交換エネルギー: E_x^LDA[ρ] = ∫ ρ(x) · ε_x(ρ(x)) dx -/
def ldaExchangeEnergy (ε_x : ℝ → ℝ) (ρ : ℝ → ℝ) : ℝ :=
  ∫ x, ρ x * ε_x (ρ x)

/-- LDA 相関エネルギー: E_c^LDA[ρ] = ∫ ρ(x) · ε_c(ρ(x)) dx -/
def ldaCorrelationEnergy (ε_c : ℝ → ℝ) (ρ : ℝ → ℝ) : ℝ :=
  ∫ x, ρ x * ε_c (ρ x)

/-- LDA を XCFunctional として構成する -/
def mkLDAFunctional (ε_x ε_c : ℝ → ℝ) : XCFunctional where
  E_xc := fun ρ => ldaExchangeEnergy ε_x ρ + ldaCorrelationEnergy ε_c ρ
  E_x := ldaExchangeEnergy ε_x
  E_c := ldaCorrelationEnergy ε_c
  decomposition := fun _ => rfl

/-- LDA 交換エネルギーの非正性:
    ε_x(ρ) ≤ 0（非負密度に対して）ならば E_x^LDA[ρ] ≤ 0

    物理: 交換はフェルミ統計に由来する引力効果であり、
    エネルギーへの寄与は常に非正 -/
theorem lda_exchange_nonpositive (ε_x : ℝ → ℝ)
    (hε : ∀ r, 0 ≤ r → ε_x r ≤ 0) :
    IsExchangeNonPositive (ldaExchangeEnergy ε_x) := by
  intro ρ hρ
  unfold ldaExchangeEnergy
  apply integral_nonpos
  intro x
  exact mul_nonpos_of_nonneg_of_nonpos (hρ x) (hε (ρ x) (hρ x))

/-- LDA 相関エネルギーの非正性:
    ε_c(ρ) ≤ 0（非負密度に対して）ならば E_c^LDA[ρ] ≤ 0 -/
theorem lda_correlation_nonpositive (ε_c : ℝ → ℝ)
    (hε : ∀ r, 0 ≤ r → ε_c r ≤ 0) :
    IsCorrelationNonPositive (ldaCorrelationEnergy ε_c) := by
  intro ρ hρ
  unfold ldaCorrelationEnergy
  apply integral_nonpos
  intro x
  exact mul_nonpos_of_nonneg_of_nonpos (hρ x) (hε (ρ x) (hρ x))

/-- LDA 汎関数全体の非正性 -/
theorem lda_xc_nonpositive (ε_x ε_c : ℝ → ℝ)
    (hεx : ∀ r, 0 ≤ r → ε_x r ≤ 0)
    (hεc : ∀ r, 0 ≤ r → ε_c r ≤ 0)
    (ρ : ℝ → ℝ) (hρ : ∀ x, 0 ≤ ρ x) :
    (mkLDAFunctional ε_x ε_c).E_xc ρ ≤ 0 :=
  xc_nonpositive_of_exchange_correlation
    (mkLDAFunctional ε_x ε_c)
    (lda_exchange_nonpositive ε_x hεx)
    (lda_correlation_nonpositive ε_c hεc)
    ρ hρ

/-- LDA は均一密度極限で定義上正しい:
    ρ(x) = ρ₀ (定数) のとき、エネルギー密度は ε_x(ρ₀) -/
theorem lda_uniform_limit (ε_x : ℝ → ℝ) :
    SatisfiesUniformLimit ε_x ε_x :=
  fun _ _ => rfl

/-- LDA の Lieb-Oxford 限界:
    ε_x(ρ) ≥ -C_LO · g(ρ) ならば E_x^LDA[ρ] ≥ -C_LO · ∫ ρ · g(ρ) -/
theorem lda_satisfies_bound (ε_x : ℝ → ℝ) (bound_density : ℝ → ℝ)
    (hbound : ∀ r, 0 ≤ r → bound_density r ≤ ε_x r)
    (ρ : ℝ → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (hint_bound : Integrable (fun x => ρ x * bound_density (ρ x)))
    (hint_ex : Integrable (fun x => ρ x * ε_x (ρ x))) :
    (∫ x, ρ x * bound_density (ρ x)) ≤ ldaExchangeEnergy ε_x ρ := by
  unfold ldaExchangeEnergy
  apply integral_mono hint_bound hint_ex
  intro x
  exact mul_le_mul_of_nonneg_left (hbound (ρ x) (hρ x)) (hρ x)

end DFT
