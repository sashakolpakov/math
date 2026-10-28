import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Big Crystalline Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCover

noncomputable section

/-!
# IntegralComparison: small polynomial presentations receive every big affine thickening

For each object of the big crystalline site of Spec C,
choose lifts of its residue-ring elements into its ambient ring. This
gives a map from the free polynomial presentation, then from a sufficiently
high finite level and its proved divided-power envelope.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Frobenius
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable (p : ℕ) [Fact p.Prime]
variable (k C : Type u) [Field k] [CharP k p] [CommRing C] [Algebra k C]
variable (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
  (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))

local notation "W" => WittVector p k

def closedRingMap : C →+* U.ring ⧸ U.ideal := (Spec.preimage U.mapToX).hom

lemma closedRingMap_spec :
    Spec.map (CommRingCat.ofHom (closedRingMap p k C U)) = U.mapToX :=
  Spec.map_preimage _

lemma closedRingMap_coefficients :
    (closedRingMap p k C U).comp (Polynomial.Frobenius.coefficientReduction p k C) =
      (Ideal.Quotient.mk U.ideal).comp U.base := by
  have h := (congrArg (fun t => U.mapToX ≫ t) (Crystalline.Presentation.affine_wittStructureMap p k C)).symm.trans U.overBase
  have h' := (congrArg
    (fun t => t ≫ Spec.map (CommRingCat.ofHom (Polynomial.Frobenius.coefficientReduction p k C)))
    (closedRingMap_spec p k C U)).trans h
  rw [← Spec.map_comp, ← Spec.map_comp] at h'
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')

def variableLift (c : C) : U.ring :=
  (Ideal.Quotient.mk_surjective (closedRingMap p k C U c)).choose

lemma variableLift_reduction (c : C) :
    Ideal.Quotient.mk U.ideal (variableLift p k C U c) = closedRingMap p k C U c :=
  (Ideal.Quotient.mk_surjective (closedRingMap p k C U c)).choose_spec

def polynomialMap : Polynomial.Frobenius.Presentation p k C →+* U.ring :=
  MvPolynomial.eval₂Hom U.base (variableLift p k C U)

lemma polynomialMap_reduction :
    (Ideal.Quotient.mk U.ideal).comp (polynomialMap p k C U) =
      (closedRingMap p k C U).comp (Polynomial.Frobenius.presentationReduction p k C) := by
  apply MvPolynomial.ringHom_ext
  · intro w
    simp only [RingHom.comp_apply, polynomialMap, Polynomial.Frobenius.presentationReduction, MvPolynomial.eval₂Hom_C]
    exact (DFunLike.congr_fun (closedRingMap_coefficients p k C U) w).symm
  · intro c
    simp only [RingHom.comp_apply, polynomialMap, Polynomial.Frobenius.presentationReduction,
      MvPolynomial.eval₂Hom_X', id_eq]
    exact variableLift_reduction p k C U c

def levelBound : ℕ := U.primeNilpotent.choose

lemma prime_pow_bound : (p : U.ring) ^ levelBound p k C U = 0 := U.primeNilpotent.choose_spec

lemma polynomialMap_kills_level :
    Polynomial.Frobenius.levelIdeal p k C (levelBound p k C U) ≤ RingHom.ker (polynomialMap p k C U) := by
  rw [Polynomial.Frobenius.levelIdeal, Ideal.span_le]
  rintro x (rfl : x = _)
  change polynomialMap p k C U ((p : Polynomial.Frobenius.Presentation p k C) ^ (levelBound p k C U + 1)) = 0
  rw [map_pow, map_natCast, pow_succ, prime_pow_bound, zero_mul]

def levelMap : Polynomial.Frobenius.Level p k C (levelBound p k C U) →+* U.ring :=
  Ideal.Quotient.lift _ (polynomialMap p k C U) (polynomialMap_kills_level p k C U)

lemma levelMap_reduction :
    (Ideal.Quotient.mk U.ideal).comp (levelMap p k C U) =
      (closedRingMap p k C U).comp (Polynomial.Frobenius.levelReduction p k C (levelBound p k C U)) := by
  apply RingHom.ext
  intro x
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun (polynomialMap_reduction p k C U) e

lemma levelMap_coefficients :
    (levelMap p k C U).comp (Polynomial.Frobenius.levelCoefficientMap p k C (levelBound p k C U)) = U.base := by
  apply RingHom.ext
  intro w
  exact MvPolynomial.eval₂Hom_C _ _ w

lemma levelMap_mapsKernel :
    Polynomial.Frobenius.levelKernel p k C (levelBound p k C U) ≤ U.ideal.comap (levelMap p k C U) := by
  intro x hx
  change levelMap p k C U x ∈ U.ideal
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := DFunLike.congr_fun (levelMap_reduction p k C U) x
  change Ideal.Quotient.mk U.ideal (levelMap p k C U x) =
    closedRingMap p k C U (Polynomial.Frobenius.levelReduction p k C (levelBound p k C U) x) at h
  rw [h, hx, map_zero]

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCover.levelBound p k C U
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

def envelopeTargetForObject :
    DividedPower.PowerEnvelope.Target W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
      (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N) where
  ring := U.ring
  ideal := U.ideal
  dividedPowers := U.dividedPowers
  fromBase := levelMap p k C U
  mapsIdeal := levelMap_mapsKernel p k C U
  baseCompatible := by rw [levelMap_coefficients]; exact U.baseCompatible

/-- A concrete divided-power map from one finite-level presentation to the
ambient ring of the given crystalline-site object. -/
def envelopeMap : DividedPowers.DPMorphism (Polynomial.Frobenius.crystallineDividedPowers p k C N) U.dividedPowers :=
  DividedPower.PowerEnvelope.lift W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
    (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N) (envelopeTargetForObject p k C U)

lemma envelopeMap_fromLevel :
    (envelopeMap p k C U).toRingHom.comp
      (DividedPower.PowerEnvelope.toEnvelope W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
        (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N)) = levelMap p k C U :=
  DividedPower.PowerEnvelope.lift_fromBase W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
    (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N) (envelopeTargetForObject p k C U)

lemma envelopeMap_fromWitt :
    (envelopeMap p k C U).toRingHom.comp (Crystalline.Presentation.baseMap p k C N) = U.base := by
  rw [Crystalline.Presentation.baseMap, ← RingHom.comp_assoc, envelopeMap_fromLevel, levelMap_coefficients]

lemma envelopeMap_reduction :
    (Ideal.Quotient.mk U.ideal).comp (envelopeMap p k C U).toRingHom =
      (closedRingMap p k C U).comp (Crystalline.Presentation.reduction p k C N) := by
  let ε := dividedPowersBot (U.ring ⧸ U.ideal)
  let qDP := DividedPower.Transfer.mapToBot U.dividedPowers
    (Ideal.Quotient.mk U.ideal) (fun _x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  let V := DividedPower.PowerEnvelope.postcomposeTarget W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
    (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N) (envelopeTargetForObject p k C U) ε qDP
  let gDP := DividedPower.Transfer.botMap (closedRingMap p k C U)
  have hleft : qDP.comp (envelopeMap p k C U) =
      DividedPower.PowerEnvelope.lift W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
        (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N) V :=
    DividedPower.PowerEnvelope.lift_postcompose W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
      (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N) (envelopeTargetForObject p k C U) ε qDP
  have hright : gDP.comp (Crystalline.Presentation.reductionDP p k C N) =
      DividedPower.PowerEnvelope.lift W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
        (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N) V := by
    apply DividedPower.PowerEnvelope.lift_unique W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
      (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N) V
    change (closedRingMap p k C U).comp ((Crystalline.Presentation.reduction p k C N).comp
      (DividedPower.PowerEnvelope.toEnvelope W (Polynomial.Frobenius.Level p k C N) (Ideal.span {(p : W)}) γ
        (Polynomial.Frobenius.levelCoefficientMap p k C N) (Polynomial.Frobenius.levelKernel p k C N))) =
      (Ideal.Quotient.mk U.ideal).comp (levelMap p k C U)
    rw [Crystalline.Presentation.reduction_fromLevel]
    exact (levelMap_reduction p k C U).symm
  exact congrArg
    (fun g : DividedPowers.DPMorphism (Polynomial.Frobenius.crystallineDividedPowers p k C N)
      (dividedPowersBot (U.ring ⧸ U.ideal)) => g.toRingHom) (hleft.trans hright.symm)

lemma quotientMap_closed :
    (BigCrystallineSite.Object.quotientMap U ((BigCrystallineSite.fromSmall.obj (Crystalline.Presentation.presentationObject p k C N)))
      (envelopeMap p k C U)).comp (Crystalline.Presentation.quotientEquiv p k C N).symm.toRingHom = closedRingMap p k C U := by
  apply RingHom.ext
  intro c
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective ((Crystalline.Presentation.quotientEquiv p k C N).symm c)
  change BigCrystallineSite.Object.quotientMap U ((BigCrystallineSite.fromSmall.obj (Crystalline.Presentation.presentationObject p k C N)))
    (envelopeMap p k C U) ((Crystalline.Presentation.quotientEquiv p k C N).symm c) = closedRingMap p k C U c
  rw [← hd]
  change Ideal.Quotient.mk U.ideal (envelopeMap p k C U d) = closedRingMap p k C U c
  have hr := DFunLike.congr_fun (envelopeMap_reduction p k C U) d
  change Ideal.Quotient.mk U.ideal (envelopeMap p k C U d) =
    closedRingMap p k C U (Crystalline.Presentation.reduction p k C N d) at hr
  rw [hr, DFunLike.congr_fun (Crystalline.Presentation.reduction_eq_quotient p k C N) d]
  change closedRingMap p k C U (Crystalline.Presentation.quotientEquiv p k C N (Ideal.Quotient.mk _ d)) =
    closedRingMap p k C U c
  rw [hd, RingEquiv.apply_symm_apply]

/-- Every big affine crystalline object maps to the image of a proved
small-site polynomial presentation. No openness of its map to X is required. -/
def presentationMorphism : U ⟶ (BigCrystallineSite.fromSmall.obj (Crystalline.Presentation.presentationObject p k C N)) where
  ringMap := envelopeMap p k C U
  overBase := envelopeMap_fromWitt p k C U
  overX := by
    change Spec.map (CommRingCat.ofHom
      (BigCrystallineSite.Object.quotientMap U ((BigCrystallineSite.fromSmall.obj (Crystalline.Presentation.presentationObject p k C N)))
        (envelopeMap p k C U))) ≫
      Spec.map (CommRingCat.ofHom (Crystalline.Presentation.quotientEquiv p k C N).symm.toRingHom) = U.mapToX
    rw [← Spec.map_comp, ← closedRingMap_spec p k C U]
    exact congrArg (fun g : C →+* U.ring ⧸ U.ideal => Spec.map (CommRingCat.ofHom g))
      (quotientMap_closed p k C U)

lemma presentation_covers : ∃ n : ℕ, Nonempty (U ⟶ (BigCrystallineSite.fromSmall.obj (Crystalline.Presentation.presentationObject p k C n))) :=
  ⟨N, ⟨presentationMorphism p k C U⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCover
