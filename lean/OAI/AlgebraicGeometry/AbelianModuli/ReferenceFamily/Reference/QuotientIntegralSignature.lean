import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.QuotientAction
import OAI.RepresentationTheory.Theta.Geometric.DiagonalEigen

/-! # Quotient Integral Signature -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The explicit period quotient has the prescribed CM signature. The
dimension is computed from the actual simultaneous scalar equations. -/

open scoped Classical BigOperators

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

def Datum.RankThreePELDatum.periodEigenSpace (τ : E →+* ℂ) : Submodule ℂ (Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s)) where
  carrier := {v | ∀ a, P.periodScalarAction a v = τ a • v}
  zero_mem' := by intro a; rw [map_zero, smul_zero]
  add_mem' := by intro v w hv hw a; rw [map_add, hv a, hw a, smul_add]
  smul_mem' := by intro c v hv a; rw [map_smul, hv a, smul_comm]

def Datum.RankThreePELDatum.periodEigenUncurry (τ : E →+* ℂ) : P.periodEigenSpace τ ≃ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.DiagonalEigen.diagonalEigenSpace (fun p : Fin s × Fin 3 => P.quotientCharacter p.1 p.2) τ where
  toFun v := ⟨fun p => v.val p.1 p.2, fun a p => congrFun (congrFun (v.property a) p.1) p.2⟩
  invFun v := ⟨fun i j => v.val (i, j), fun a => funext fun i => funext fun j => v.property a (i, j)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Datum.RankThreePELDatum.referenceEmbedding_ne_conjugate (hP : P.IsAdmissible) (i : Fin s) :
    (P.embeddings i).toRingHom ≠
      (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom := by
  intro he
  have hp : (i, false) = (i, true) := hP.1.1 (by
    apply AlgHom.ext
    intro a
    exact congrArg (fun f : E →+* ℂ => f a) he)
  exact Bool.false_ne_true (congrArg Prod.snd hp)

theorem Datum.RankThreePELDatum.quotientCharacter_count (hP : P.IsAdmissible) (τ : E →+* ℂ) :
    Fintype.card {p : Fin s × Fin 3 // P.quotientCharacter p.1 p.2 = τ} =
      ∑ i : Fin s,
        if τ = (P.embeddings i).toRingHom then P.firstLieRank i
        else if τ = (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom
          then 3 - P.firstLieRank i else 0 := by
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_three]
  have hne := P.referenceEmbedding_ne_conjugate hP i
  by_cases hi : i = P.distinguished <;>
    cases hs : P.compactSigns i <;>
    by_cases he : τ = (P.embeddings i).toRingHom <;>
    by_cases hc : τ = (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom <;>
    simp_all [Datum.RankThreePELDatum.quotientCharacter, Datum.RankThreePELDatum.firstLieRank] <;> aesop

theorem Datum.RankThreePELDatum.periodEigenSpace_finrank (hP : P.IsAdmissible) (τ : E ≃ₐ[ℚ] E) :
    Module.finrank ℂ (P.periodEigenSpace (P.μ.comp τ.toRingHom)) =
      P.lieRank τ := by
  rw [(P.periodEigenUncurry (P.μ.comp τ.toRingHom)).finrank_eq,
    RepresentationTheory.Theta.Geometric.DiagonalEigen.diagonalEigen_finrank, P.quotientCharacter_count hP]
  rfl

end

/-! Restricting the CM action to the ring of integers retains exactly the
same eigenspaces, and hence the full prescribed signature. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

def Datum.RankThreePELDatum.periodIntegerAction : NumberField.RingOfIntegers E →+*
    Module.End ℂ (Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s)) :=
  P.periodScalarAction.comp (algebraMap (NumberField.RingOfIntegers E) E)

def Datum.RankThreePELDatum.integralPeriodEigenSpace (τ : E →+* ℂ) : Submodule ℂ (Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s)) where
  carrier := {v | ∀ a : NumberField.RingOfIntegers E, P.periodIntegerAction a v = τ (a : E) • v}
  zero_mem' := by intro a; rw [map_zero, smul_zero]
  add_mem' := by intro v w hv hw a; rw [map_add, hv a, hw a, smul_add]
  smul_mem' := by intro c v hv a; rw [map_smul, hv a, smul_comm]

omit [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.integralPeriodEigenSpace_eq (τ : E →+* ℂ) :
    P.integralPeriodEigenSpace τ = P.periodEigenSpace τ := by
  apply Submodule.ext
  intro v
  constructor
  · intro hv a
    funext i j
    change P.quotientCharacter i j a * v i j = τ a * v i j
    by_cases hz : v i j = 0
    · rw [hz, mul_zero, mul_zero]
    · have hc : P.quotientCharacter i j = τ :=
        IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers E) (by
          intro b
          exact mul_right_cancel₀ hz (congrFun (congrFun (hv b) i) j))
      rw [hc]
  · intro hv a
    exact hv (a : E)

theorem Datum.RankThreePELDatum.integralPeriodEigenSpace_finrank (hP : P.IsAdmissible) (τ : E ≃ₐ[ℚ] E) :
    Module.finrank ℂ (P.integralPeriodEigenSpace (P.μ.comp τ.toRingHom)) =
      P.lieRank τ := by
  rw [P.integralPeriodEigenSpace_eq]
  exact P.periodEigenSpace_finrank hP τ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
