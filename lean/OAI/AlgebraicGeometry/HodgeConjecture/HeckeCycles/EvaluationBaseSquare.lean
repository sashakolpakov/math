import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction

/-! # Evaluation Base Square -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM

noncomputable section

/-! The actual finite Witt evaluation DVR lies over the q-adic integral
model, with commuting generic, arithmetic, and residue squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftBase.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM

variable {q : ℕ} [Fact q.Prime]
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

def integralMap : ℤ_[q] →+* V.carrier :=
  (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) V.carrier).comp (Witt.LiftBase.CM.fromPadic q (Witt.ArithmeticBase.CM.k (q := q)))

def fieldMap : ℚ_[q] →+* L :=
  (algebraMap (Witt.ArithmeticBase.CM.Generic.F q) L).comp (Witt.ArithmeticBase.CM.Generic.padicToField q)

theorem generic_compatible :
    (fieldMap (L := L) (q := q)).comp (algebraMap ℤ_[q] ℚ_[q]) =
      (algebraMap V.carrier L).comp (integralMap V) := by
  ext x
  change algebraMap (Witt.ArithmeticBase.CM.Generic.F q) L (Witt.ArithmeticBase.CM.Generic.padicToField q (algebraMap ℤ_[q] ℚ_[q] x)) =
    algebraMap V.carrier L (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) V.carrier (Witt.LiftBase.CM.fromPadic q (Witt.ArithmeticBase.CM.k (q := q)) x))
  rw [Witt.ArithmeticBase.CM.Generic.padicToField_integral]
  exact (IsScalarTower.algebraMap_apply (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L _).symm.trans
    (IsScalarTower.algebraMap_apply (Witt.ArithmeticBase.CM.W (q := q)) V.carrier L _)

def integralBase : Spec (.of V.carrier) ⟶ Spec (.of ℤ_[q]) :=
  Spec.map (CommRingCat.ofHom (integralMap V))

def fieldBase : Spec (.of L) ⟶ Spec (.of ℚ_[q]) :=
  Spec.map (CommRingCat.ofHom (fieldMap (L := L) (q := q)))

theorem generic_square :
    fieldBase (L := L) (q := q) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ_[q] ℚ_[q])) =
      ValuativePoints.CM.genericBase (R := V.carrier) (L := L) ≫ integralBase V := by
  change Spec.map (CommRingCat.ofHom (fieldMap (L := L) (q := q))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ_[q] ℚ_[q])) =
    Spec.map (CommRingCat.ofHom (algebraMap V.carrier L)) ≫
      Spec.map (CommRingCat.ofHom (integralMap V))
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (generic_compatible V))

omit [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L] in
theorem residue_compatible :
    (LiftedReduction.CM.geometricResidue (Witt.EvaluationDVR.CM.geometricResidueIso V)).comp (integralMap V) =
      (algebraMap (ZMod q) (Witt.ArithmeticBase.CM.k (q := q))).comp (PadicInt.toZMod : ℤ_[q] →+* ZMod q) := by
  ext x
  change (Witt.EvaluationDVR.CM.geometricResidueIso V).symm
      (IsLocalRing.residue V.carrier
        (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) V.carrier (Witt.LiftBase.CM.fromPadic q (Witt.ArithmeticBase.CM.k (q := q)) x))) = _
  rw [← V.residue_compatible]
  change (Witt.LiftBase.CM.residueEquiv q (Witt.ArithmeticBase.CM.k (q := q)))
    (V.residueIso.symm (V.residueIso
      (IsLocalRing.residue (Witt.ArithmeticBase.CM.W (q := q)) (Witt.LiftBase.CM.fromPadic q (Witt.ArithmeticBase.CM.k (q := q)) x)))) = _
  rw [RingEquiv.symm_apply_apply]
  exact (Witt.LiftBase.CM.fromPadic_residue q (Witt.ArithmeticBase.CM.k (q := q)) x).trans
    (RingHom.congr_fun (Subsingleton.elim
      (ZMod.castHom (dvd_refl q) (Witt.ArithmeticBase.CM.k (q := q)))
      (algebraMap (ZMod q) (Witt.ArithmeticBase.CM.k (q := q)))) (PadicInt.toZMod x))

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K}
  {j : M.QadicChoice q} (hden : Nat.Coprime q M.arithmetic.denominator)

omit [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L] in
theorem arithmetic_square :
    integralBase V ≫ QadicModelMap.CM.integralBase j M.arithmetic.denominator hden =
      Witt.EvaluationDVR.CM.evaluatedBase (j := j) V hden := by
  change Spec.map (CommRingCat.ofHom (integralMap V)) ≫
      Spec.map (CommRingCat.ofHom
        (QadicModelMap.CM.integralMap j M.arithmetic.denominator hden)) =
    Spec.map (CommRingCat.ofHom (Witt.EvaluationDVR.CM.evaluatedArithmeticMap (j := j) V hden))
  rw [← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM
