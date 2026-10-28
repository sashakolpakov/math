import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeFieldPoints

/-! # Evaluation Residue Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM

noncomputable section

/-! The evaluation DVR's actual residue map defines the same test point
over the prime-field special fiber. The comparison is constructed from
the proved residue square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM

variable {q : ℕ} [Fact q.Prime] {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

def geometricBase : Spec (.of (Witt.ArithmeticBase.CM.k (q := q))) ⟶ Spec (.of (ZMod q)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (Witt.ArithmeticBase.CM.k (q := q))))

def residueBase : Spec (.of (Witt.ArithmeticBase.CM.k (q := q))) ⟶ Spec (.of ℤ_[q]) :=
  Spec.map (CommRingCat.ofHom (LiftedReduction.CM.geometricResidue (Witt.EvaluationDVR.CM.geometricResidueIso V))) ≫ EvaluationBaseSquare.CM.integralBase V

theorem residue_square :
    geometricBase (q := q) ≫ Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)) =
      residueBase V := by
  change Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (Witt.ArithmeticBase.CM.k (q := q)))) ≫
      Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)) =
    Spec.map (CommRingCat.ofHom (LiftedReduction.CM.geometricResidue (Witt.EvaluationDVR.CM.geometricResidueIso V))) ≫
      Spec.map (CommRingCat.ofHom (EvaluationBaseSquare.CM.integralMap V))
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (EvaluationBaseSquare.CM.residue_compatible V).symm)

def testIso :
    (Over.map (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))).obj
      (Over.mk (geometricBase (q := q))) ≅
    ValuativePoints.CM.specialTest (EvaluationBaseSquare.CM.integralBase V) (LiftedReduction.CM.geometricResidue (Witt.EvaluationDVR.CM.geometricResidueIso V)) :=
  PrimeFieldPoints.CM.testIso _ _ _ (residue_square V)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM
