import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftBase
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import Mathlib.RingTheory.Localization.FractionRing

/-! # Arithmetic Base -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM

/-! The Witt-vector lifting base is compatible with the exact residue map
and q-adic choice returned by CMPoints for the original arithmetic model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftBase.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)
  (hden : Nat.Coprime q M.arithmetic.denominator)

abbrev k := AlgebraicClosure (ZMod q)
abbrev W := WittVector q (k (q := q))

def arithmeticMap : M.arithmetic.R →+* W (q := q) :=
  (LiftBase.CM.fromPadic q (k (q := q))).comp
    (QadicModelMap.CM.integralMap j M.arithmetic.denominator hden)

theorem arithmeticMap_residue (x : M.arithmetic.R) :
    LiftBase.CM.residueEquiv q (k (q := q))
      (IsLocalRing.residue (W (q := q)) (arithmeticMap (j := j) hden x)) =
      algebraMap (ZMod q) (k (q := q)) (R.residue x) := by
  have hc := RingHom.congr_fun
    (QadicModelMap.CM.integralMap_residue j M.arithmetic.denominator hden
      R.residue R.residue_compatibility) x
  have he : (ZMod.castHom (dvd_refl q) (k (q := q))) =
      algebraMap (ZMod q) (k (q := q)) := Subsingleton.elim _ _
  exact (LiftBase.CM.fromPadic_residue q (k (q := q))
    (QadicModelMap.CM.integralMap j M.arithmetic.denominator hden x)).trans
      ((congrArg (fun z : ZMod q => (z.cast : k (q := q))) hc).trans
        (RingHom.congr_fun he (R.residue x)))

def residueIso : k (q := q) ≃+* IsLocalRing.ResidueField (W (q := q)) :=
  (LiftBase.CM.residueEquiv q (k (q := q))).symm

theorem residue_compatible :
    (IsLocalRing.residue (W (q := q))).comp (arithmeticMap (j := j) hden) =
      (residueIso (q := q)).toRingHom.comp
        ((algebraMap (ZMod q) (k (q := q))).comp R.residue) := by
  ext x
  apply (LiftBase.CM.residueEquiv q (k (q := q))).injective
  exact (arithmeticMap_residue R hden x).trans
    ((LiftBase.CM.residueEquiv q (k (q := q))).apply_symm_apply _).symm

def wittBase : Spec (.of (W (q := q))) ⟶ M.arithmetic.base :=
  Spec.map (CommRingCat.ofHom (arithmeticMap (j := j) hden))

theorem geometric_square :
    Spec.map (CommRingCat.ofHom (residueIso (q := q)).toRingHom) ≫ R.geometricBase =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (W (q := q)))) ≫ wittBase (j := j) hden := by
  change Spec.map (CommRingCat.ofHom (residueIso (q := q)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom ((algebraMap (ZMod q) (k (q := q))).comp R.residue)) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (W (q := q)))) ≫
        Spec.map (CommRingCat.ofHom (arithmeticMap (j := j) hden))
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (residue_compatible R hden).symm)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

/-! The Witt lifting field contains the chosen q-adic field. The
induced number-field embedding agrees with the same integral arithmetic
map used for the geometric point lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftBase.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM

variable (q : ℕ) [Fact q.Prime]

abbrev F := FractionRing (W (q := q))

theorem fromPadic_injective : Function.Injective (LiftBase.CM.fromPadic q (k (q := q))) :=
  (WittVector.map_injective (ZMod.castHom (dvd_refl q) (k (q := q)))
    (ZMod.castHom (dvd_refl q) (k (q := q))).injective).comp
      (WittVector.equiv q).symm.injective

def padicIntegralToField : ℤ_[q] →+* F q :=
  (algebraMap (W (q := q)) (F q)).comp (LiftBase.CM.fromPadic q (k (q := q)))

theorem padicIntegralToField_injective : Function.Injective (padicIntegralToField q) :=
  (IsFractionRing.injective (W (q := q)) (F q)).comp (fromPadic_injective q)

def padicToField : ℚ_[q] →+* F q :=
  IsFractionRing.lift (padicIntegralToField_injective q)

theorem padicToField_integral (x : ℤ_[q]) :
    padicToField q (algebraMap ℤ_[q] ℚ_[q] x) = padicIntegralToField q x :=
  IsFractionRing.lift_algebraMap (padicIntegralToField_injective q) x

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  (j : M.QadicChoice q) (hden : Nat.Coprime q M.arithmetic.denominator)

def numberFieldEmbedding : M.arithmetic.extension.carrier →+* F q :=
  (padicToField q).comp (QadicModelMap.CM.localFieldEmbedding j)

theorem arithmeticMap_generic :
    (algebraMap (W (q := q)) (F q)).comp (arithmeticMap (j := j) hden) =
      (numberFieldEmbedding j).comp M.arithmetic.toField := by
  ext x
  have he := RingHom.congr_fun
    (QadicModelMap.CM.integralMap_generic j M.arithmetic.denominator
      M.arithmetic.denominator_ne_zero hden) x
  exact (padicToField_integral q
    (QadicModelMap.CM.integralMap j M.arithmetic.denominator hden x)).symm.trans
      (congrArg (padicToField q) he)

def fractionBase : Spec (.of (F q)) ⟶ Spec (.of (W (q := q))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (W (q := q)) (F q)))

def numberFieldBase : Spec (.of (F q)) ⟶ Spec (.of M.arithmetic.extension.carrier) :=
  Spec.map (CommRingCat.ofHom (numberFieldEmbedding j))

theorem generic_square :
    fractionBase (q := q) ≫ wittBase (j := j) hden =
      numberFieldBase j ≫ M.arithmetic.generic := by
  change Spec.map (CommRingCat.ofHom (algebraMap (W (q := q)) (F q))) ≫
      Spec.map (CommRingCat.ofHom (arithmeticMap (j := j) hden)) =
    Spec.map (CommRingCat.ofHom (numberFieldEmbedding j)) ≫
      Spec.map (CommRingCat.ofHom M.arithmetic.toField)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (arithmeticMap_generic j hden))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

end

end OAI
