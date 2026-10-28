import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeGenerators

/-! # Phase Basis -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseBasis.TestTransport

noncomputable section

/-! Columns of the retained PEL phase matrix are images of the
original rational coordinate basis vectors. -/

open scoped Classical _root_.Matrix

variable (E : Type) [Field E] [NumberField E]
  {J : Type*} [Fintype J] [DecidableEq J]
  (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ))

theorem coefficientVectorCoordinates_basis (j : J) :
    CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E (e.symm (Pi.single j 1))) =
      Pi.single j 1 := by
  rw [show AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E (e.symm (Pi.single j 1)) =
    (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (e.symm (Pi.single j 1) i)) from rfl,
    CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational, LinearEquiv.apply_symm_apply]
  funext i
  by_cases h : i = j
  · subst i
    simp
  · simp [h]

theorem coefficientVectorCoordinates_basis_projection {R : Type*} [CommRing R]
    (f : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles →+* R) (j : J) :
    (fun k => f (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
      (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E (e.symm (Pi.single j 1))) k)) = Pi.single j 1 := by
  rw [coefficientVectorCoordinates_basis]
  funext k
  by_cases h : k = j
  · subst k
    simp
  · simp [h]

variable [NumberField.IsCMField E] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

theorem pelPhaseMatrix_column (g : P.FiniteSpecialUnitary) (i j : J) :
    PhaseCoordinates.TestTransport.pelPhaseMatrix E P e g i j = CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
      (g.val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E (e.symm (Pi.single j 1)))) i := by
  have h := congr_fun (PhaseCoordinates.TestTransport.pelPhaseAction_coordinates E P e g
    (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E (e.symm (Pi.single j 1)))) i
  rw [coefficientVectorCoordinates_basis] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseBasis.TestTransport
