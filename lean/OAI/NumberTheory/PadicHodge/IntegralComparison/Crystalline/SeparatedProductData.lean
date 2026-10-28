import OAI.NumberTheory.PadicHodge.IntegralComparison.SeparatedAffineIntersection
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PrescribedLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Separated Product Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductData

noncomputable section

/-!
# IntegralComparison: the closed quotient for products over a separated scheme

The actual closed fiber product over X embeds in the closed fiber product
over the affine base. The latter is the residue of the divided-power
pushout. Thus the former is a proved quotient of that pushout.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
variable (U V : BigCrystallineSite.Object p B J δ f)

def Initial := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.Initial B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers

instance initialCommRing : CommRing (Initial f U V) :=
  @DividedPower.PrescribedPushout.initialCommRing B U.ring V.ring
    inferInstance inferInstance inferInstance U.base.toAlgebra V.base.toAlgebra
    U.ideal U.dividedPowers V.ideal V.dividedPowers

def initialIdeal : Ideal (Initial f U V) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.initialIdeal B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers

def initialDP : DividedPowers (initialIdeal f U V) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.initialDP B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers

def leftInitial : DividedPowers.DPMorphism U.dividedPowers (initialDP f U V) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.leftInitial B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers

def rightInitial : DividedPowers.DPMorphism V.dividedPowers (initialDP f U V) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.rightInitial B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers

abbrev Residue := Initial f U V ⧸ initialIdeal f U V

def leftResidue : U.ring ⧸ U.ideal →+* Residue f U V :=
  Ideal.quotientMap (initialIdeal f U V) (leftInitial f U V).toRingHom
    (Ideal.map_le_iff_le_comap.mp (leftInitial f U V).ideal_comp)

def rightResidue : V.ring ⧸ V.ideal →+* Residue f U V :=
  Ideal.quotientMap (initialIdeal f U V) (rightInitial f U V).toRingHom
    (Ideal.map_le_iff_le_comap.mp (rightInitial f U V).ideal_comp)

lemma base_pullback : IsPullback (Spec.map (CommRingCat.ofHom (leftResidue f U V)))
    (Spec.map (CommRingCat.ofHom (rightResidue f U V))) (U.mapToX ≫ f) (V.mapToX ≫ f) := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  rw [U.overBase, V.overBase, ← Spec.map_comp, ← Spec.map_comp]
  exact (DividedPower.PushoutResidue.schemePullback B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers).flip

abbrev ClosedRing : CommRingCat.{u} :=
  SeparatedAffineIntersection.CoordinateRing U.mapToX V.mapToX

variable [IsSeparated f]

def closedFst : Spec (ClosedRing f U V) ⟶ Spec (CommRingCat.of (U.ring ⧸ U.ideal)) :=
  SeparatedAffineIntersection.fst U.mapToX V.mapToX f

def closedSnd : Spec (ClosedRing f U V) ⟶ Spec (CommRingCat.of (V.ring ⧸ V.ideal)) :=
  SeparatedAffineIntersection.snd U.mapToX V.mapToX f

lemma closed_pullback : IsPullback (closedFst f U V) (closedSnd f U V) U.mapToX V.mapToX :=
  SeparatedAffineIntersection.isPullback U.mapToX V.mapToX f

def embedding : Spec (ClosedRing f U V) ⟶ Spec (CommRingCat.of (Residue f U V)) :=
  SeparatedAffineIntersection.embedding U.mapToX V.mapToX f
    (Spec.map (CommRingCat.ofHom (leftResidue f U V)))
    (Spec.map (CommRingCat.ofHom (rightResidue f U V))) (base_pullback f U V)

instance embedding_closed : IsClosedImmersion (embedding f U V) :=
  SeparatedAffineIntersection.embedding_closed U.mapToX V.mapToX f _ _ _

def residueReduction : Residue f U V →+* ClosedRing f U V := (Spec.preimage (embedding f U V)).hom

lemma residueReduction_surjective : Function.Surjective (residueReduction f U V) :=
  SeparatedAffineIntersection.spec_preimage_surjective (embedding f U V)

lemma residueReduction_left : (residueReduction f U V).comp (leftResidue f U V) =
    (Spec.preimage (closedFst f U V)).hom := by
  have he : CommRingCat.ofHom ((residueReduction f U V).comp (leftResidue f U V)) =
      Spec.preimage (closedFst f U V) := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (leftResidue f U V) ≫ Spec.preimage (embedding f U V)) = _
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact SeparatedAffineIntersection.embedding_fst U.mapToX V.mapToX f _ _ _
  exact congrArg CommRingCat.Hom.hom he

lemma residueReduction_right : (residueReduction f U V).comp (rightResidue f U V) =
    (Spec.preimage (closedSnd f U V)).hom := by
  have he : CommRingCat.ofHom ((residueReduction f U V).comp (rightResidue f U V)) =
      Spec.preimage (closedSnd f U V) := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (rightResidue f U V) ≫ Spec.preimage (embedding f U V)) = _
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact SeparatedAffineIntersection.embedding_snd U.mapToX V.mapToX f _ _ _
  exact congrArg CommRingCat.Hom.hom he

def reduction : DividedPowers.DPMorphism (initialDP f U V) (dividedPowersBot (ClosedRing f U V)) :=
  DividedPower.Transfer.mapToBot (initialDP f U V)
    ((residueReduction f U V).comp (Ideal.Quotient.mk (initialIdeal f U V))) (by
      intro x hx
      change residueReduction f U V (Ideal.Quotient.mk (initialIdeal f U V) x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])

lemma reduction_surjective : Function.Surjective (reduction f U V) :=
  (residueReduction_surjective f U V).comp Ideal.Quotient.mk_surjective

def leftReduction : DividedPowers.DPMorphism U.dividedPowers (dividedPowersBot (ClosedRing f U V)) :=
  (reduction f U V).comp (leftInitial f U V)

def rightReduction : DividedPowers.DPMorphism V.dividedPowers (dividedPowersBot (ClosedRing f U V)) :=
  (reduction f U V).comp (rightInitial f U V)

lemma reductions_agree : (leftReduction f U V).toRingHom.comp U.base =
    (rightReduction f U V).toRingHom.comp V.base := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  apply RingHom.ext
  intro b
  exact congrArg (reduction f U V)
    (DFunLike.congr_fun (DividedPower.Pushout.maps_agree B U.ring V.ring
      U.ideal U.dividedPowers V.ideal V.dividedPowers) b)

def prescribedReduction : DividedPowers.DPMorphism (initialDP f U V)
    (dividedPowersBot (ClosedRing f U V)) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.initialReduction B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (ClosedRing f U V)
    (leftReduction f U V) (rightReduction f U V) (reductions_agree f U V)

lemma prescribedReduction_surjective : Function.Surjective (prescribedReduction f U V) := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  have he : reduction f U V = prescribedReduction f U V :=
    DividedPower.PushoutLift.lift_unique B U.ring V.ring
      U.ideal U.dividedPowers V.ideal V.dividedPowers
      (leftReduction f U V) (rightReduction f U V) (reductions_agree f U V)
      (reduction f U V) rfl rfl
  exact he ▸ reduction_surjective f U V

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductData
