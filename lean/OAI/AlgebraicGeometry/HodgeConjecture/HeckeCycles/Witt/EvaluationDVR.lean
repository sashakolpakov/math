import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts

/-! # Evaluation DVR -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM

noncomputable section

/-! Finite extensions of the actual Witt lifting field have constructed
complete evaluation DVRs. Their residue map remains the geometric map
chosen by CMPoints; no evaluation-DVR existence hypothesis is added. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (q : ℕ) [Fact q.Prime]

theorem fractionCharZero : CharZero (ArithmeticBase.CM.Generic.F q) where
  cast_injective m n h := Nat.cast_injective ((ArithmeticBase.CM.Generic.padicToField q).injective (by
    simpa only [map_natCast] using h))

theorem residueAlgebraicallyClosed : IsAlgClosed (IsLocalRing.ResidueField (ArithmeticBase.CM.W (q := q))) :=
  IsAlgClosed.of_ringEquiv (ArithmeticBase.CM.k (q := q)) _ (ArithmeticBase.CM.residueIso (q := q))

def evaluationDVR (L : Type) [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L] [Module.Finite (ArithmeticBase.CM.Generic.F q) L]
    [Algebra (ArithmeticBase.CM.W (q := q)) L] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L] :
    Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L := by
  let : CharZero (ArithmeticBase.CM.Generic.F q) := fractionCharZero q
  let : IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticBase.CM.W (q := q))) (ArithmeticBase.CM.W (q := q)) :=
    LiftBase.CM.complete q (ArithmeticBase.CM.k (q := q))
  let : HenselianLocalRing (ArithmeticBase.CM.W (q := q)) := Isogenies.NeighborCounting.AdicTransport.Lifts.complete_local_henselian _
  let : IsAlgClosed (IsLocalRing.ResidueField (ArithmeticBase.CM.W (q := q))) := residueAlgebraicallyClosed q
  exact Isogenies.NeighborCounting.EvaluationDVRLifts.evaluationDVR (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L

variable {q : ℕ} [Fact q.Prime]
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.W (q := q)) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L)

def geometricResidueIso : ArithmeticBase.CM.k (q := q) ≃+* IsLocalRing.ResidueField V.carrier :=
  (ArithmeticBase.CM.residueIso (q := q)).trans V.residueIso

theorem residue_square :
    (IsLocalRing.residue V.carrier).comp (algebraMap (ArithmeticBase.CM.W (q := q)) V.carrier) =
      V.residueIso.toRingHom.comp (IsLocalRing.residue (ArithmeticBase.CM.W (q := q))) := by
  ext x
  exact (V.residue_compatible x).symm

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K}
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)
  (hden : Nat.Coprime q M.arithmetic.denominator)

def evaluatedArithmeticMap : M.arithmetic.R →+* V.carrier :=
  (algebraMap (ArithmeticBase.CM.W (q := q)) V.carrier).comp (ArithmeticBase.CM.arithmeticMap (j := j) hden)

theorem evaluatedArithmeticMap_residue :
    (IsLocalRing.residue V.carrier).comp (evaluatedArithmeticMap (j := j) V hden) =
      (geometricResidueIso V).toRingHom.comp
        ((algebraMap (ZMod q) (ArithmeticBase.CM.k (q := q))).comp R.residue) := by
  ext x
  exact (V.residue_compatible (ArithmeticBase.CM.arithmeticMap (j := j) hden x)).symm.trans
    (congrArg V.residueIso (RingHom.congr_fun (ArithmeticBase.CM.residue_compatible R hden) x))

def evaluatedBase : Spec (.of V.carrier) ⟶ M.arithmetic.base :=
  Spec.map (CommRingCat.ofHom (evaluatedArithmeticMap (j := j) V hden))

theorem geometric_square :
    Spec.map (CommRingCat.ofHom (geometricResidueIso V).toRingHom) ≫ R.geometricBase =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue V.carrier)) ≫ evaluatedBase (j := j) V hden := by
  change Spec.map (CommRingCat.ofHom (geometricResidueIso V).toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((algebraMap (ZMod q) (ArithmeticBase.CM.k (q := q))).comp R.residue)) =
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue V.carrier)) ≫
      Spec.map (CommRingCat.ofHom (evaluatedArithmeticMap (j := j) V hden))
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (evaluatedArithmeticMap_residue V R hden).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM
