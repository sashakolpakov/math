import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Frobenius

/-! # Presentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

noncomputable section

/-!
# IntegralComparison: Frobenius on actual affine crystalline thickenings

The polynomial divided-power presentations reduce to the given affine
scheme. Their constructed Frobenius maps are proved to reduce to q-power
Frobenius on its coordinate ring.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Frobenius

variable (p : ℕ) [Fact p.Prime]
variable (k C : Type u) [Field k] [Fintype k] [CharP k p] [CommRing C] [Algebra k C]
variable (n : ℕ)

local notation "W" => WittVector p k
local notation "Pₙ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Frobenius.Level p k C n
local notation "Dₙ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Frobenius.CrystallinePresentation p k C n
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

def residueTarget : DividedPower.PowerEnvelope.Target W Pₙ (Ideal.span {(p : W)}) γ
    (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n) where
  ring := C
  ideal := ⊥
  dividedPowers := dividedPowersBot C
  fromBase := Polynomial.Frobenius.levelReduction p k C n
  mapsIdeal := fun _x hx => hx
  baseCompatible :=
    (DividedPower.Transfer.mapToBot γ
      ((Polynomial.Frobenius.levelReduction p k C n).comp (Polynomial.Frobenius.levelCoefficientMap p k C n))
      (fun _x hx => Polynomial.Frobenius.baseIdeal_le_levelKernel p k C n hx)).isDPMorphism

def reductionDP : DividedPowers.DPMorphism (Polynomial.Frobenius.crystallineDividedPowers p k C n) (dividedPowersBot C) :=
  DividedPower.PowerEnvelope.lift W Pₙ (Ideal.span {(p : W)}) γ (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n)
    (residueTarget p k C n)

abbrev reduction : Dₙ →+* C := (reductionDP p k C n).toRingHom

omit [Fintype k] in
lemma reduction_fromLevel :
    (reduction p k C n).comp
      (DividedPower.PowerEnvelope.toEnvelope W Pₙ (Ideal.span {(p : W)}) γ (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n)) =
        Polynomial.Frobenius.levelReduction p k C n :=
  DividedPower.PowerEnvelope.lift_fromBase W Pₙ (Ideal.span {(p : W)}) γ (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n)
    (residueTarget p k C n)

def baseMap : W →+* Dₙ :=
  (DividedPower.PowerEnvelope.toEnvelope W Pₙ (Ideal.span {(p : W)}) γ
    (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n)).comp (Polynomial.Frobenius.levelCoefficientMap p k C n)

omit [Fintype k] in
lemma reduction_fromWitt :
    (reduction p k C n).comp (baseMap p k C n) = Polynomial.Frobenius.coefficientReduction p k C := by
  rw [baseMap, ← RingHom.comp_assoc, reduction_fromLevel, Polynomial.Frobenius.levelReduction_coefficients]

/-- The constructed divided-power Frobenius lifts the actual q-power
Frobenius of the original coordinate ring. -/
lemma frobenius_reduction :
    (reduction p k C n).comp (Polynomial.Frobenius.presentationFrobenius p k C n).toRingHom =
      (FiniteField.frobeniusAlgHom k C).toRingHom.comp (reduction p k C n) := by
  have h := EnvelopeFunctor.endomorphism_natural W Pₙ
    (Ideal.span {(p : W)}) γ (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n)
    (Polynomial.Frobenius.baseIdeal_le_levelKernel p k C n) (DividedPowers.DPMorphism.id γ)
    (Polynomial.Frobenius.levelFrobenius p k C n) (Polynomial.Frobenius.levelFrobenius_coefficients p k C n)
    (Polynomial.Frobenius.levelFrobenius_preserves_kernel p k C n) (residueTarget p k C n)
    (DividedPower.Transfer.botMap (FiniteField.frobeniusAlgHom k C).toRingHom)
    (Polynomial.Frobenius.levelFrobenius_reduction p k C n).symm
  exact congrArg
    (fun g : DividedPowers.DPMorphism (Polynomial.Frobenius.crystallineDividedPowers p k C n) (dividedPowersBot C) =>
      g.toRingHom) h

/-- The closed subscheme of the crystalline presentation is exactly Spec C. -/
def quotientEquiv : (Dₙ ⧸ Polynomial.Frobenius.crystallineIdeal p k C n) ≃+* C :=
  (EnvelopeResidue.quotientEquiv W Pₙ (Ideal.span {(p : W)}) γ
    (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n) (Polynomial.Frobenius.baseIdeal_le_levelKernel p k C n)).symm.trans
    (RingHom.quotientKerEquivOfSurjective (Polynomial.Frobenius.levelReduction_surjective p k C n))

omit [Fintype k] in
lemma quotientEquiv_fromLevel (x : Pₙ) :
    quotientEquiv p k C n (Ideal.Quotient.mk _
      (DividedPower.PowerEnvelope.toEnvelope W Pₙ (Ideal.span {(p : W)}) γ
        (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n) x)) = Polynomial.Frobenius.levelReduction p k C n x := by
  let e := EnvelopeResidue.quotientEquiv W Pₙ (Ideal.span {(p : W)}) γ
    (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n) (Polynomial.Frobenius.baseIdeal_le_levelKernel p k C n)
  have he : e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _
      (DividedPower.PowerEnvelope.toEnvelope W Pₙ (Ideal.span {(p : W)}) γ
        (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n) x) := rfl
  change RingHom.quotientKerEquivOfSurjective (Polynomial.Frobenius.levelReduction_surjective p k C n)
    (e.symm _) = _
  rw [← he, e.symm_apply_apply]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ x

omit [Fintype k] in
lemma quotientEquiv_fromWitt (w : W) :
    quotientEquiv p k C n (Ideal.Quotient.mk _ (baseMap p k C n w)) =
      Polynomial.Frobenius.coefficientReduction p k C w := by
  change quotientEquiv p k C n (Ideal.Quotient.mk _
    (DividedPower.PowerEnvelope.toEnvelope W Pₙ (Ideal.span {(p : W)}) γ
      (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n) (Polynomial.Frobenius.levelCoefficientMap p k C n w))) = _
  rw [quotientEquiv_fromLevel]
  exact DFunLike.congr_fun (Polynomial.Frobenius.levelReduction_coefficients p k C n) w

def affineScheme : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k C)))

omit [Fintype k] [CharP k p] in
lemma affine_wittStructureMap :
    Witt.Crystalline.wittStructureMap p k (affineScheme k C) =
      Spec.map (CommRingCat.ofHom (Polynomial.Frobenius.coefficientReduction p k C)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap k C)) ≫
    Spec.map (CommRingCat.ofHom WittVector.constantCoeff) = _
  rw [← Spec.map_comp]
  rfl

def residueSchemeIso : Spec (CommRingCat.of (Dₙ ⧸ Polynomial.Frobenius.crystallineIdeal p k C n)) ≅
    Spec (CommRingCat.of C) :=
  (Scheme.Spec.mapIso (quotientEquiv p k C n).toCommRingCatIso.op).symm

/-- The polynomial divided-power presentation is an object of the same
crystalline site used in the cohomology construction. -/
def presentationObject :
    Witt.Crystalline.CrystallineObject p k (affineScheme k C) where
  ring := CommRingCat.of Dₙ
  base := baseMap p k C n
  ideal := Polynomial.Frobenius.crystallineIdeal p k C n
  dividedPowers := Polynomial.Frobenius.crystallineDividedPowers p k C n
  baseCompatible :=
    (DividedPower.PowerEnvelope.envelopeTarget W Pₙ (Ideal.span {(p : W)}) γ
      (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n) (Polynomial.Frobenius.baseIdeal_le_levelKernel p k C n)).baseCompatible
  primeNilpotent := Polynomial.Frobenius.crystalline_prime_nilpotent p k C n
  nilIdeal := fun _x hx => Polynomial.Frobenius.crystalline_nilIdeal p k C n hx
  openMap := (residueSchemeIso p k C n).hom
  isOpenImmersion := IsOpenImmersion.of_isIso (residueSchemeIso p k C n).hom
  overBase := by
    rw [affine_wittStructureMap]
    change Spec.map (CommRingCat.ofHom (quotientEquiv p k C n).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.Frobenius.coefficientReduction p k C)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Polynomial.Frobenius.crystallineIdeal p k C n))) ≫
        Spec.map (CommRingCat.ofHom (baseMap p k C n))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    apply (quotientEquiv p k C n).injective
    change quotientEquiv p k C n ((quotientEquiv p k C n).symm (Polynomial.Frobenius.coefficientReduction p k C w)) =
      quotientEquiv p k C n (Ideal.Quotient.mk _ (baseMap p k C n w))
    rw [RingEquiv.apply_symm_apply, quotientEquiv_fromWitt]

def quotientReductionDP :
    DividedPowers.DPMorphism (Polynomial.Frobenius.crystallineDividedPowers p k C n) (dividedPowersBot C) :=
  DividedPower.Transfer.mapToBot (Polynomial.Frobenius.crystallineDividedPowers p k C n)
    ((quotientEquiv p k C n).toRingHom.comp (Ideal.Quotient.mk (Polynomial.Frobenius.crystallineIdeal p k C n)))
    (by
      intro x hx
      change quotientEquiv p k C n (Ideal.Quotient.mk _ x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])

omit [Fintype k] in
lemma quotientReduction_eq : quotientReductionDP p k C n = reductionDP p k C n := by
  apply DividedPower.PowerEnvelope.lift_unique W Pₙ (Ideal.span {(p : W)}) γ
    (Polynomial.Frobenius.levelCoefficientMap p k C n) (Polynomial.Frobenius.levelKernel p k C n) (residueTarget p k C n)
  apply RingHom.ext
  intro x
  exact quotientEquiv_fromLevel p k C n x

omit [Fintype k] in
lemma reduction_eq_quotient : reduction p k C n =
    (quotientEquiv p k C n).toRingHom.comp (Ideal.Quotient.mk (Polynomial.Frobenius.crystallineIdeal p k C n)) :=
  (congrArg (fun g : DividedPowers.DPMorphism (Polynomial.Frobenius.crystallineDividedPowers p k C n)
    (dividedPowersBot C) => g.toRingHom) (quotientReduction_eq p k C n)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
