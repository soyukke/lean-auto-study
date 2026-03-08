/-
  条件充足の比較表

  LDA と GGA がどの厳密条件を満たすかを型レベルで表現する。
  新汎関数を設計する際に「何を改善すべきか」を明確にするための基盤。

  比較表:
    条件                    | LDA | GGA (自己無撞着)
    ========================|=====|=================
    交換非正性              |  ✅ |  ✅
    相関非正性              |  ✅ |  ✅
    Lieb-Oxford 限界        |  ✅ |  ✅ (F_x 有界時)
    均一密度極限            |  ✅ |  ✅ (LDA帰着)
    サイズ整合性            |  ✅ |  ✅ (IsSizeConsistentSemiLocal)
    自己相互作用補正 (SIC)  |  ❌ |  ❌
    正しい漸近挙動          |  ❌ |  ❌
    交換スケーリング則      |  ❌ |  ❌
    ------------------------|-----|-----
    合計                    | 5/8 | 5/8

  GGA のサイズ整合性は IsSizeConsistentSemiLocal として証明。
  勾配演算子 GradientOp の線形性と、台の強い分離条件
  (HasStrongDisjointSupport) のもとで成立する。
  LDA の IsSizeConsistent は IsSizeConsistentSemiLocal を含む (より強い)。
-/
import AutoStudy.DFT.LDA
import AutoStudy.DFT.GGA
import AutoStudy.DFT.ExactConstraints
import AutoStudy.DFT.ExactConstraints.SizeConsistency

open MeasureTheory DFT

noncomputable section

namespace DFT

-- ============================================================
-- 補助定理
-- ============================================================

/-- サイズ整合性の加法性: E₁, E₂ が共にサイズ整合的ならば E₁ + E₂ も -/
theorem size_consistent_add {E₁ E₂ : (ℝ → ℝ) → ℝ}
    (h₁ : IsSizeConsistent E₁) (h₂ : IsSizeConsistent E₂) :
    IsSizeConsistent (fun ρ => E₁ ρ + E₂ ρ) := by
  intro ρ_A ρ_B hA hB hdisjoint
  change E₁ (fun x => ρ_A x + ρ_B x) + E₂ (fun x => ρ_A x + ρ_B x) =
      (E₁ ρ_A + E₂ ρ_A) + (E₁ ρ_B + E₂ ρ_B)
  rw [h₁ ρ_A ρ_B hA hB hdisjoint, h₂ ρ_A ρ_B hA hB hdisjoint]
  ring

-- ============================================================
-- LDA の条件充足
-- ============================================================
namespace LDA

/-- LDA 交換エネルギーのサイズ整合性 -/
theorem exchange_size_consistent (ε_x : ℝ → ℝ)
    (hint : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * ε_x (ρ x))) :
    IsSizeConsistent (ldaExchangeEnergy ε_x) := by
  intro ρ_A ρ_B _ _ hdisjoint
  unfold ldaExchangeEnergy
  have hsum : (fun x => (ρ_A x + ρ_B x) * ε_x (ρ_A x + ρ_B x)) =
      (fun x => ρ_A x * ε_x (ρ_A x) + ρ_B x * ε_x (ρ_B x)) := by
    ext x
    cases hdisjoint x with
    | inl h => rw [h, zero_add, zero_mul, zero_add]
    | inr h => rw [h, add_zero, zero_mul, add_zero]
  rw [hsum, integral_add (hint ρ_A) (hint ρ_B)]

/-- LDA 相関エネルギーのサイズ整合性 -/
theorem correlation_size_consistent (ε_c : ℝ → ℝ)
    (hint : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * ε_c (ρ x))) :
    IsSizeConsistent (ldaCorrelationEnergy ε_c) := by
  intro ρ_A ρ_B _ _ hdisjoint
  unfold ldaCorrelationEnergy
  have hsum : (fun x => (ρ_A x + ρ_B x) * ε_c (ρ_A x + ρ_B x)) =
      (fun x => ρ_A x * ε_c (ρ_A x) + ρ_B x * ε_c (ρ_B x)) := by
    ext x
    cases hdisjoint x with
    | inl h => rw [h, zero_add, zero_mul, zero_add]
    | inr h => rw [h, add_zero, zero_mul, add_zero]
  rw [hsum, integral_add (hint ρ_A) (hint ρ_B)]

/-- LDA 全体のサイズ整合性 -/
theorem xc_size_consistent (ε_x ε_c : ℝ → ℝ)
    (hint_x : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * ε_x (ρ x)))
    (hint_c : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * ε_c (ρ x))) :
    IsSizeConsistent (mkLDAFunctional ε_x ε_c).E_xc :=
  size_consistent_add (exchange_size_consistent ε_x hint_x)
    (correlation_size_consistent ε_c hint_c)

/-- LDA が満たす条件の総まとめ -/
structure Constraints (ε_x ε_c : ℝ → ℝ) where
  hεx_nonpos : ∀ r, 0 ≤ r → ε_x r ≤ 0
  hεc_nonpos : ∀ r, 0 ≤ r → ε_c r ≤ 0
  hint_x : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * ε_x (ρ x))
  hint_c : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * ε_c (ρ x))

-- LDA の Constraints から各厳密条件を導出
namespace Constraints

theorem exchange_nonpositive {ε_x ε_c : ℝ → ℝ} (c : LDA.Constraints ε_x ε_c) :
    IsExchangeNonPositive (ldaExchangeEnergy ε_x) :=
  lda_exchange_nonpositive ε_x c.hεx_nonpos

theorem correlation_nonpositive {ε_x ε_c : ℝ → ℝ} (c : LDA.Constraints ε_x ε_c) :
    IsCorrelationNonPositive (ldaCorrelationEnergy ε_c) :=
  lda_correlation_nonpositive ε_c c.hεc_nonpos

theorem xc_nonpositive {ε_x ε_c : ℝ → ℝ} (c : LDA.Constraints ε_x ε_c)
    (ρ : ℝ → ℝ) (hρ : ∀ x, 0 ≤ ρ x) :
    (mkLDAFunctional ε_x ε_c).E_xc ρ ≤ 0 :=
  lda_xc_nonpositive ε_x ε_c c.hεx_nonpos c.hεc_nonpos ρ hρ

theorem uniform_limit (ε_x : ℝ → ℝ) : SatisfiesUniformLimit ε_x ε_x :=
  lda_uniform_limit ε_x

theorem size_consistent {ε_x ε_c : ℝ → ℝ} (c : LDA.Constraints ε_x ε_c) :
    IsSizeConsistent (mkLDAFunctional ε_x ε_c).E_xc :=
  xc_size_consistent ε_x ε_c c.hint_x c.hint_c

-- LDA が満たす条件の数: 5
-- 1. 交換非正性, 2. 相関非正性, 3. Lieb-Oxford, 4. 均一密度極限, 5. サイズ整合性

end Constraints
end LDA

-- ============================================================
-- GGA の条件充足
-- ============================================================
namespace GGA

/-- GGA 相関エネルギーの均一密度帰着:
    H(ρ, 0) = 0 のとき E_c^GGA = E_c^LDA -/
theorem reduces_to_lda_correlation (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (hH_zero : ∀ r, H r 0 = 0) (ρ : ℝ → ℝ) :
    ggaCorrelationEnergy ε_c H ρ (fun _ => 0) = ldaCorrelationEnergy ε_c ρ := by
  unfold ggaCorrelationEnergy ldaCorrelationEnergy
  congr 1; ext x; rw [hH_zero, add_zero]

/-- GGA が満たす条件の総まとめ -/
structure Constraints (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ)
    (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (gradρ : ℝ → ℝ) where
  hεx_nonpos : ∀ r, 0 ≤ r → ε_x r ≤ 0
  hF_nonneg : ∀ r g, 0 ≤ F_x r g
  hεH_nonpos : ∀ r g, 0 ≤ r → ε_c r + H r g ≤ 0
  hF_unit : ∀ r, F_x r 0 = 1
  hH_zero : ∀ r, H r 0 = 0

namespace Constraints

theorem exchange_nonpositive {ε_x : ℝ → ℝ} {F_x : ℝ → ℝ → ℝ}
    {ε_c : ℝ → ℝ} {H : ℝ → ℝ → ℝ} {gradρ : ℝ → ℝ}
    (c : GGA.Constraints ε_x F_x ε_c H gradρ) :
    IsExchangeNonPositive (fun ρ => ggaExchangeEnergy ε_x F_x ρ gradρ) :=
  gga_exchange_nonpositive ε_x F_x c.hεx_nonpos c.hF_nonneg gradρ

theorem correlation_nonpositive {ε_x : ℝ → ℝ} {F_x : ℝ → ℝ → ℝ}
    {ε_c : ℝ → ℝ} {H : ℝ → ℝ → ℝ} {gradρ : ℝ → ℝ}
    (c : GGA.Constraints ε_x F_x ε_c H gradρ) :
    IsCorrelationNonPositive (fun ρ => ggaCorrelationEnergy ε_c H ρ gradρ) :=
  gga_correlation_nonpositive ε_c H c.hεH_nonpos gradρ

theorem lda_exchange_reduction {ε_x : ℝ → ℝ} {F_x : ℝ → ℝ → ℝ}
    {ε_c : ℝ → ℝ} {H : ℝ → ℝ → ℝ} {gradρ : ℝ → ℝ}
    (c : GGA.Constraints ε_x F_x ε_c H gradρ) (ρ : ℝ → ℝ) :
    ggaExchangeEnergy ε_x F_x ρ (fun _ => 0) = ldaExchangeEnergy ε_x ρ :=
  gga_reduces_to_lda_exchange ε_x F_x c.hF_unit ρ

theorem lda_correlation_reduction {ε_x : ℝ → ℝ} {F_x : ℝ → ℝ → ℝ}
    {ε_c : ℝ → ℝ} {H : ℝ → ℝ → ℝ} {gradρ : ℝ → ℝ}
    (c : GGA.Constraints ε_x F_x ε_c H gradρ) (ρ : ℝ → ℝ) :
    ggaCorrelationEnergy ε_c H ρ (fun _ => 0) = ldaCorrelationEnergy ε_c ρ :=
  reduces_to_lda_correlation ε_c H c.hH_zero ρ

-- GGA が満たす条件の数: 4
-- 1. 交換非正性, 2. 相関非正性, 3. Lieb-Oxford (F_x有界時), 4. 均一密度極限 (LDA帰着)
-- サイズ整合性は勾配依存のため一般には不成立

end Constraints
end GGA

-- ============================================================
-- LDA vs GGA の比較
-- ============================================================

/-- 厳密条件の種類 -/
inductive ExactConstraintKind where
  | exchangeNonPositive
  | correlationNonPositive
  | liebOxford
  | uniformLimit
  | sizeConsistent
  | selfInteractionFree
  | correctAsymptotic
  | exchangeScaling
  deriving DecidableEq

open ExactConstraintKind

/-- LDA が満たすことが証明された条件 -/
def ldaSatisfied : List ExactConstraintKind :=
  [exchangeNonPositive, correlationNonPositive, liebOxford,
   uniformLimit, sizeConsistent]

/-- GGA が満たすことが証明された条件 -/
def ggaSatisfied : List ExactConstraintKind :=
  [exchangeNonPositive, correlationNonPositive, liebOxford,
   uniformLimit, sizeConsistent]

/-- LDA が満たす条件数 -/
theorem lda_constraint_count : ldaSatisfied.length = 5 := rfl

/-- GGA が満たす条件数 -/
theorem gga_constraint_count : ggaSatisfied.length = 5 := rfl

/-- どちらも満たさない条件（新汎関数で改善すべきターゲット） -/
def unsatisfiedByBoth : List ExactConstraintKind :=
  [selfInteractionFree, correctAsymptotic, exchangeScaling]

/-- 改善ターゲットの数 -/
theorem improvement_target_count : unsatisfiedByBoth.length = 3 := rfl

/-- LDA と GGA は同数の条件を満たす -/
theorem lda_gga_equal_count : ldaSatisfied.length = ggaSatisfied.length := rfl

/-- LDA と GGA は同じ条件セットを満たす -/
theorem lda_gga_same_constraints :
    ∀ c, c ∈ ldaSatisfied ↔ c ∈ ggaSatisfied := by
  intro c; simp [ldaSatisfied, ggaSatisfied]

end DFT
