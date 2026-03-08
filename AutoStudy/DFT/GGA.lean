/-
  一般化勾配近似 (GGA)

  LDA を密度の勾配情報で拡張した近似:
    E_xc^GGA[ρ] = ∫ f(ρ(x), |Dρ(x)|) dx

  交換エネルギーの場合、enhancement factor F_x(s) を導入:
    E_x^GGA[ρ] = ∫ ρ(x) · ε_x^LDA(ρ(x)) · F_x(s(x)) dx
    s = |Dρ| / (2 k_F ρ) は無次元化された勾配

  GGA は LDA より多くの厳密条件を満たすことができる。
  PBE (Perdew-Burke-Ernzerhof) が代表的な GGA 汎関数。
-/
import AutoStudy.DFT.ExchangeCorrelation
import AutoStudy.DFT.ExactConstraints
import AutoStudy.DFT.ExactConstraints.SizeConsistency
import AutoStudy.DFT.LDA

open MeasureTheory DFT

noncomputable section

namespace DFT

/-- GGA 交換エネルギー:
    E_x^GGA[ρ, Dρ] = ∫ ρ(x) · ε_x(ρ(x)) · F_x(ρ(x), |Dρ(x)|) dx

    ε_x: LDA 交換エネルギー密度
    F_x: enhancement factor（≥ 0 であり、Dρ = 0 で F_x = 1 に戻る） -/
def ggaExchangeEnergy (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ) (ρ gradρ : ℝ → ℝ) : ℝ :=
  ∫ x, ρ x * ε_x (ρ x) * F_x (ρ x) (gradρ x)

/-- GGA 相関エネルギー:
    E_c^GGA[ρ, Dρ] = ∫ ρ(x) · (ε_c(ρ(x)) + H(ρ(x), |Dρ(x)|)) dx

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
    Dρ = 0 のとき F_x(ρ, 0) = 1 ならば
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

-- ============================================================
-- 自己無撞着 GGA (勾配を密度の関数として扱う)
-- ============================================================

/-- 線形勾配演算子: D(f + g) = Df + Dg を満たす -/
structure GradientOp where
  apply : (ℝ → ℝ) → (ℝ → ℝ)
  additive : ∀ f g : ℝ → ℝ,
    apply (fun x => f x + g x) = fun x => apply f x + apply g x

/-- 台の強い分離条件: 密度と勾配が共に分離する。
    物理的には、密度がある領域で完全に 0 ならその領域での勾配も 0。 -/
def HasStrongDisjointSupport (ρ_A ρ_B : ℝ → ℝ) (D : GradientOp) : Prop :=
  ∀ x, (ρ_A x = 0 ∧ D.apply ρ_A x = 0) ∨ (ρ_B x = 0 ∧ D.apply ρ_B x = 0)

/-- 強い分離は通常の分離を含む -/
theorem HasStrongDisjointSupport.toDisjoint {ρ_A ρ_B : ℝ → ℝ} {D : GradientOp}
    (h : HasStrongDisjointSupport ρ_A ρ_B D) :
    ∀ x, ρ_A x = 0 ∨ ρ_B x = 0 := by
  intro x; cases h x with
  | inl h => exact Or.inl h.1
  | inr h => exact Or.inr h.1

/-- 半局所汎関数のサイズ整合性:
    密度と勾配が共に分離する場合に E[ρ_A + ρ_B] = E[ρ_A] + E[ρ_B] -/
def IsSizeConsistentSemiLocal (E : (ℝ → ℝ) → ℝ) (D : GradientOp) : Prop :=
  ∀ ρ_A ρ_B : ℝ → ℝ,
    (∀ x, 0 ≤ ρ_A x) → (∀ x, 0 ≤ ρ_B x) →
    HasStrongDisjointSupport ρ_A ρ_B D →
    E (fun x => ρ_A x + ρ_B x) = E ρ_A + E ρ_B

/-- 局所的サイズ整合性は通常のサイズ整合性から従う -/
theorem IsSizeConsistent.toSemiLocal {E : (ℝ → ℝ) → ℝ} (D : GradientOp)
    (h : IsSizeConsistent E) : IsSizeConsistentSemiLocal E D := by
  intro ρ_A ρ_B hA hB hstrong
  exact h ρ_A ρ_B hA hB hstrong.toDisjoint

/-- 半局所サイズ整合性の加法性 -/
theorem size_consistent_semilocal_add {E₁ E₂ : (ℝ → ℝ) → ℝ} {D : GradientOp}
    (h₁ : IsSizeConsistentSemiLocal E₁ D) (h₂ : IsSizeConsistentSemiLocal E₂ D) :
    IsSizeConsistentSemiLocal (fun ρ => E₁ ρ + E₂ ρ) D := by
  intro ρ_A ρ_B hA hB hdisjoint
  change E₁ (fun x => ρ_A x + ρ_B x) + E₂ (fun x => ρ_A x + ρ_B x) =
      (E₁ ρ_A + E₂ ρ_A) + (E₁ ρ_B + E₂ ρ_B)
  rw [h₁ ρ_A ρ_B hA hB hdisjoint, h₂ ρ_A ρ_B hA hB hdisjoint]
  ring

/-- 自己無撞着 GGA 交換エネルギー: 勾配を密度から自動計算 -/
def scGGAExchangeEnergy (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ)
    (D : GradientOp) (ρ : ℝ → ℝ) : ℝ :=
  ggaExchangeEnergy ε_x F_x ρ (D.apply ρ)

/-- 自己無撞着 GGA 相関エネルギー: 勾配を密度から自動計算 -/
def scGGACorrelationEnergy (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (D : GradientOp) (ρ : ℝ → ℝ) : ℝ :=
  ggaCorrelationEnergy ε_c H ρ (D.apply ρ)

/-- 自己無撞着 GGA を XCFunctional として構成する -/
def mkSCGGAFunctional (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ)
    (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (D : GradientOp) : XCFunctional where
  E_xc := fun ρ => scGGAExchangeEnergy ε_x F_x D ρ + scGGACorrelationEnergy ε_c H D ρ
  E_x := scGGAExchangeEnergy ε_x F_x D
  E_c := scGGACorrelationEnergy ε_c H D
  decomposition := fun _ => rfl

/-- 自己無撞着 GGA 交換エネルギーのサイズ整合性 -/
theorem scGGA_exchange_size_consistent (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ) (D : GradientOp)
    (hint : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * ε_x (ρ x) * F_x (ρ x) (D.apply ρ x))) :
    IsSizeConsistentSemiLocal (scGGAExchangeEnergy ε_x F_x D) D := by
  intro ρ_A ρ_B _ _ hdisjoint
  unfold scGGAExchangeEnergy ggaExchangeEnergy
  have hgrad : ∀ x, D.apply (fun x => ρ_A x + ρ_B x) x =
      D.apply ρ_A x + D.apply ρ_B x :=
    fun x => congr_fun (D.additive ρ_A ρ_B) x
  have hsum : (fun x => (ρ_A x + ρ_B x) * ε_x (ρ_A x + ρ_B x) *
      F_x (ρ_A x + ρ_B x) (D.apply (fun x => ρ_A x + ρ_B x) x)) =
      (fun x => ρ_A x * ε_x (ρ_A x) * F_x (ρ_A x) (D.apply ρ_A x) +
                ρ_B x * ε_x (ρ_B x) * F_x (ρ_B x) (D.apply ρ_B x)) := by
    ext x; rw [hgrad]
    cases hdisjoint x with
    | inl h => simp [h.1, h.2]
    | inr h => simp [h.1, h.2]
  rw [hsum, integral_add (hint ρ_A) (hint ρ_B)]

/-- 自己無撞着 GGA 相関エネルギーのサイズ整合性 -/
theorem scGGA_correlation_size_consistent (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (D : GradientOp)
    (hint : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * (ε_c (ρ x) + H (ρ x) (D.apply ρ x)))) :
    IsSizeConsistentSemiLocal (scGGACorrelationEnergy ε_c H D) D := by
  intro ρ_A ρ_B _ _ hdisjoint
  unfold scGGACorrelationEnergy ggaCorrelationEnergy
  have hgrad : ∀ x, D.apply (fun x => ρ_A x + ρ_B x) x =
      D.apply ρ_A x + D.apply ρ_B x :=
    fun x => congr_fun (D.additive ρ_A ρ_B) x
  have hsum : (fun x => (ρ_A x + ρ_B x) *
      (ε_c (ρ_A x + ρ_B x) + H (ρ_A x + ρ_B x)
        (D.apply (fun x => ρ_A x + ρ_B x) x))) =
      (fun x => ρ_A x * (ε_c (ρ_A x) + H (ρ_A x) (D.apply ρ_A x)) +
                ρ_B x * (ε_c (ρ_B x) + H (ρ_B x) (D.apply ρ_B x))) := by
    ext x; rw [hgrad]
    cases hdisjoint x with
    | inl h => simp [h.1, h.2]
    | inr h => simp [h.1, h.2]
  rw [hsum, integral_add (hint ρ_A) (hint ρ_B)]

/-- 自己無撞着 GGA 全体のサイズ整合性 -/
theorem scGGA_xc_size_consistent (ε_x : ℝ → ℝ) (F_x : ℝ → ℝ → ℝ)
    (ε_c : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (D : GradientOp)
    (hint_x : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * ε_x (ρ x) * F_x (ρ x) (D.apply ρ x)))
    (hint_c : ∀ ρ : ℝ → ℝ, Integrable (fun x => ρ x * (ε_c (ρ x) + H (ρ x) (D.apply ρ x)))) :
    IsSizeConsistentSemiLocal (mkSCGGAFunctional ε_x F_x ε_c H D).E_xc D :=
  size_consistent_semilocal_add
    (scGGA_exchange_size_consistent ε_x F_x D hint_x)
    (scGGA_correlation_size_consistent ε_c H D hint_c)

end DFT
