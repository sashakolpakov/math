import OAI.AlgebraicGeometry.PELModuli.CMPoints.EmbeddedBasis
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodCoordinates

/-! # Basis Hodge -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BasisHodge

noncomputable section

/-! The rational orthogonal basis transports the three rank-one CM
Hodge structures to the component's actual rational vector space. -/

open scoped Classical TensorProduct

open _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

def rationalBasisEquiv (b : Basis (Fin 3) E (Fin 3 → E)) :
    (Fin 3 → E) ≃ₗ[ℚ] (Fin 3 → E) := b.equivFun.symm.restrictScalars ℚ

def ambientBasisEquiv (b : Basis (Fin 3) E (Fin 3 → E)) :
    Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
  LinearEquiv.piCongrRight (fun i =>
    (EmbeddedBasis.embeddedBasisEquiv (P.embeddings i).toRingHom b).prodCongr
      (EmbeddedBasis.embeddedBasisEquiv (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom b))

theorem cmPeriodCoordinates_tmul (z : ℂ) (x : Fin 3 → E) :
    PeriodCoordinates.cmPeriodCoordinates P hP (z ⊗ₜ[ℚ] x) = z • Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings x := by
  funext i
  apply Prod.ext <;> funext j <;>
    simp [PeriodCoordinates.cmPeriodCoordinates_first, PeriodCoordinates.cmPeriodCoordinates_second,
      Products.hodgePiCoordinates, Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]

omit [NumberField E] [NumberField.IsCMField E] in
theorem ambientBasisEquiv_rational (b : Basis (Fin 3) E (Fin 3 → E)) (x : Fin 3 → E) :
    ambientBasisEquiv P b (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings x) =
      Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings (rationalBasisEquiv b x) := by
  funext i
  apply Prod.ext
  · exact EmbeddedBasis.embeddedBasisEquiv_rational (P.embeddings i).toRingHom b x
  · exact EmbeddedBasis.embeddedBasisEquiv_rational (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom b x

theorem cmPeriodCoordinates_basis_change (b : Basis (Fin 3) E (Fin 3 → E))
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    PeriodCoordinates.cmPeriodCoordinates P hP ((rationalBasisEquiv b).baseChange ℚ ℂ _ _ x) =
      ambientBasisEquiv P b (PeriodCoordinates.cmPeriodCoordinates P hP x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    rw [LinearEquiv.baseChange_tmul, cmPeriodCoordinates_tmul, cmPeriodCoordinates_tmul,
      map_smul, ambientBasisEquiv_rational]
  | add x y hx hy => simp only [map_add, hx, hy]

def basisCMHodge (b : Basis (Fin 3) E (Fin 3 → E)) :
    ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E) :=
  (PeriodCoordinates.coordinateCMHodge P hP).transport (rationalBasisEquiv b)

def basisCMDecomposition (b : Basis (Fin 3) E (Fin 3 → E)) :
    ComplexMultiplication.Decomposition.CM.CMDecomposition (basisCMHodge P hP b) :=
  Transport.cmDecompositionTransport (PeriodCoordinates.coordinateCMDecomposition P hP) (rationalBasisEquiv b)

theorem basisCMRealization_hasCMH1 (b : Basis (Fin 3) E (Fin 3 → E))
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (basisCMHodge P hP b)) : R.abelianVariety.HasCMH1 :=
  ⟨R.h1HodgeStructure, R.h1HodgeStructure_holomorphic,
    R.h1HodgeStructure_antiholomorphic,
    ⟨Transport.cmDecompositionTransport (basisCMDecomposition P hP b) R.comparison⟩⟩

theorem basisCMHodge_holomorphic (b : Basis (Fin 3) E (Fin 3 → E))
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    x ∈ (basisCMHodge P hP b).holomorphic ↔
      PeriodCoordinates.coordinateSignCondition P ((ambientBasisEquiv P b).symm (PeriodCoordinates.cmPeriodCoordinates P hP x)) := by
  obtain ⟨y, rfl⟩ := ((rationalBasisEquiv b).baseChange ℚ ℂ _ _).surjective x
  rw [basisCMHodge, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.transport_holomorphic,
    PeriodCoordinates.coordinateCMHodge_holomorphic, cmPeriodCoordinates_basis_change,
    LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BasisHodge
