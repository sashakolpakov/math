import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity

/-! # One Index -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneIndex.Quadratic

noncomputable section

/-! Remove the unique multiplicity index from the AdelicTheta rational frame,
retaining the exact native symplectic pairing. -/

open scoped Classical
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

def singleFrameIndex (n : ℕ) : (Fin n × Fin 3) ≃ (Fin n × (Fin 3 × Fin 1)) where
  toFun i := (i.1, i.2, 0)
  invFun i := (i.1, i.2.1)
  left_inv _ := rfl
  right_inv i := by
    have h : i.2.2 = 0 := Subsingleton.elim _ _
    exact Prod.ext rfl (Prod.ext rfl h.symm)

def singlePhaseReindex (n : ℕ) :
    (((Fin n × (Fin 3 × Fin 1)) ⊕ (Fin n × (Fin 3 × Fin 1))) → ℚ) ≃ₗ[ℚ]
      (((Fin n × Fin 3) ⊕ (Fin n × Fin 3)) → ℚ) :=
  LinearEquiv.funCongrLeft ℚ ℚ (Equiv.sumCongr (singleFrameIndex n) (singleFrameIndex n))

theorem singlePhaseReindex_pairing (n : ℕ)
    (x y : ((Fin n × (Fin 3 × Fin 1)) ⊕ (Fin n × (Fin 3 × Fin 1))) → ℚ) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (singlePhaseReindex n x) (singlePhaseReindex n y) =
      RepresentationTheory.Theta.Adelic.DataTheta.standardPairing x y :=
  (singleFrameIndex n).sum_comp (fun i => x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i))

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (a : E) (ha : IsCMField.complexConj E a = a) (ha0 : a ≠ 0)
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 1
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (MultiplicityOne.Quadratic.directSkewUnit E δ hδ hδ0 a ha ha0))
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E)
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (MultiplicityOne.Quadratic.directSkewUnit E δ hδ hδ0 a ha ha0) A)

def flattenedRationalCoordinates :
    (Fin 3 → E) ≃ₗ[ℚ] ((Sum (Fin A.places × Fin 3) (Fin A.places × Fin 3)) → ℚ) :=
  (OneCoordinates.Quadratic.directRationalCoordinates E δ hδ hδ0 b hb hb0 a ha ha0 A B).trans (singlePhaseReindex A.places)

theorem flattenedRationalCoordinates_pairing
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (MultiplicityOne.Quadratic.directGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0))
    (x y : Fin 3 → E) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing
      (flattenedRationalCoordinates E δ hδ hδ0 b hb hb0 a ha ha0 A B x)
      (flattenedRationalCoordinates E δ hδ hδ0 b hb hb0 a ha ha0 A B y) =
      Algebra.trace ℚ E (δ * (a * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)) := by
  change RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (singlePhaseReindex _ _) (singlePhaseReindex _ _) = _
  rw [singlePhaseReindex_pairing]
  exact OneCoordinates.Quadratic.directRationalCoordinates_pairing E δ hδ hδ0 b hb hb0 a ha ha0 A B hCoord x y

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneIndex.Quadratic
