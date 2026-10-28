import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalOpen
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearActionMatrices

/-! # Phase Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseCoordinates.TestTransport

noncomputable section

/-! The original finite PEL action in a retained rational phase basis. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalOpen.Approximation

variable (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  {J : Type*} [Fintype J] [DecidableEq J]
  (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ))

def pelPhaseAction : P.FiniteSpecialUnitary →*
    ((J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) ≃ₗ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] (J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)) where
  toFun g := (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).symm.trans
    ((g.val.restrictScalars AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles).trans (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).apply_symm_apply x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e (g.val (h.val ((CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).symm x))) =
      CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e (g.val ((CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).symm
        (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e (h.val ((CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).symm x)))))
    rw [LinearEquiv.symm_apply_apply]

def pelPhaseMatrix (g : P.FiniteSpecialUnitary) : Matrix J J AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles :=
  LinearActionMatrices.TestTransport.linearActionMatrix (pelPhaseAction E P e) g

theorem pelPhaseMatrix_mulVec (g : P.FiniteSpecialUnitary) (x : J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) :
    pelPhaseMatrix E P e g *ᵥ x = pelPhaseAction E P e g x :=
  LinearActionMatrices.TestTransport.linearActionMatrix_mulVec (pelPhaseAction E P e) g x

theorem pelPhaseMatrix_one : pelPhaseMatrix E P e 1 = 1 :=
  LinearActionMatrices.TestTransport.linearActionMatrix_one (pelPhaseAction E P e)

theorem pelPhaseAction_continuous :
    Continuous (fun z : P.FiniteSpecialUnitary × (J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) =>
      pelPhaseAction E P e z.1 z.2) :=
  (CoefficientVectorCoordinates.TestTransport.coefficientVectorHomeomorph E e).continuous.comp
    ((PrincipalOpen.Approximation.pelFinite_action_continuous E P).comp (continuous_fst.prodMk
      ((CoefficientVectorCoordinates.TestTransport.coefficientVectorHomeomorph E e).symm.continuous.comp continuous_snd)))

theorem pelPhaseMatrix_continuous : Continuous (pelPhaseMatrix E P e) :=
  LinearActionMatrices.TestTransport.linearActionMatrix_continuous (pelPhaseAction E P e) (pelPhaseAction_continuous E P e)

theorem pelPhaseAction_coordinates (g : P.FiniteSpecialUnitary)
    (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    pelPhaseAction E P e g (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e x) =
      CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e (g.val x) := by
  change CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e (g.val
    ((CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).symm (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e x))) = _
  rw [LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseCoordinates.TestTransport
