import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.Generators
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

/-! # Crystalline Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CrystallineFrame

noncomputable section

/-!
# IntegralComparison: finite polynomial envelopes as original crystalline objects

The verified envelopes have exactly the prescribed closed fibre and
define objects of the original Witt crystalline site. Their actual
divided-power Frobenius reduces to the q-power map on that fibre.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (C σ : Type u) [CommRing C] [Algebra k C] (x : σ → C) (n : ℕ)
  (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] C))

local notation "W" => WittVector p k
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.ideal p k n
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.dividedPowers p k n
local notation "P" => MvPolynomial σ B
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.kernel p k C σ x n
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.Ring p k C σ x n
local notation "IE" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.ideal p k C σ x n
local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.dividedPowers p k C σ x n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.quotientEquiv p k C σ x n hx

theorem quotientEquiv_polynomial (a : P) :
    e (Ideal.Quotient.mk IE (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) I a)) =
      PolynomialPresentation.reduction p k C σ x n a := by
  let d := EnvelopeResidue.quotientEquiv B P J δ (algebraMap B P) I
    (Ideal.map_le_iff_le_comap.mp (PolynomialPresentation.base_le p k C σ x n))
  have hd : d (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk IE (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) I a) := rfl
  change RingHom.quotientKerEquivOfSurjective (PolynomialPresentation.reduction_surjective p k C σ x n hx) (d.symm _) = _
  rw [← hd, d.symm_apply_apply]
  rfl

theorem quotientEquiv_base (w : W) :
    e (Ideal.Quotient.mk IE (PolynomialPresentation.base p k C σ x n w)) =
      algebraMap k C (WittVector.constantCoeff w) := by
  change e (Ideal.Quotient.mk IE (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) I
    (MvPolynomial.C (Truncated.Witt.quotient p k n w)))) = _
  rw [quotientEquiv_polynomial, PolynomialPresentation.reduction, MvPolynomial.eval₂Hom_C]
  rfl

def residueSchemeIso : Spec (CommRingCat.of (E ⧸ IE)) ≅ Spec (CommRingCat.of C) :=
  (Scheme.Spec.mapIso (e).toCommRingCatIso.op).symm

/-- The finite polynomial envelope is an object of the original crystalline site. -/
def object : Witt.Crystalline.CrystallineObject p k (Crystalline.Presentation.affineScheme k C) where
  ring := CommRingCat.of E
  base := PolynomialPresentation.base p k C σ x n
  ideal := IE
  dividedPowers := ε
  baseCompatible := PolynomialPresentation.base_isDPMorphism p k C σ x n
  primeNilpotent := PolynomialPresentation.prime_nilpotent p k C σ x n
  nilIdeal := fun _a ha => PolynomialPresentation.nilIdeal p k C σ x n ha
  openMap := (residueSchemeIso p k C σ x n hx).hom
  isOpenImmersion := IsOpenImmersion.of_isIso (residueSchemeIso p k C σ x n hx).hom
  overBase := by
    rw [Crystalline.Presentation.affine_wittStructureMap]
    change Spec.map (CommRingCat.ofHom (e).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap k C).comp WittVector.constantCoeff)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk IE)) ≫
        Spec.map (CommRingCat.ofHom (PolynomialPresentation.base p k C σ x n))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    apply (e).injective
    change e ((e).symm (algebraMap k C (WittVector.constantCoeff w))) =
      e (Ideal.Quotient.mk IE (PolynomialPresentation.base p k C σ x n w))
    rw [RingEquiv.apply_symm_apply, quotientEquiv_base]

def residueTarget : DividedPower.PowerEnvelope.Target B P J δ (algebraMap B P) I where
  ring := C
  ideal := ⊥
  dividedPowers := dividedPowersBot C
  fromBase := PolynomialPresentation.reduction p k C σ x n
  mapsIdeal := fun _a ha => ha
  baseCompatible := (DividedPower.Transfer.mapToBot δ
    ((PolynomialPresentation.reduction p k C σ x n).comp (algebraMap B P))
    (fun _b hb => Ideal.map_le_iff_le_comap.mp (PolynomialPresentation.base_le p k C σ x n) hb)).isDPMorphism

def reductionDP : DividedPowers.DPMorphism ε (dividedPowersBot C) :=
  DividedPower.PowerEnvelope.lift B P J δ (algebraMap B P) I (residueTarget p k C σ x n)

theorem reduction_polynomial :
    (reductionDP p k C σ x n).toRingHom.comp (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) I) =
      PolynomialPresentation.reduction p k C σ x n :=
  DividedPower.PowerEnvelope.lift_fromBase B P J δ (algebraMap B P) I (residueTarget p k C σ x n)

/-- The actual envelope Frobenius induces the q-power map of the prescribed closed fibre. -/
theorem frobenius_reduction :
    (reductionDP p k C σ x n).toRingHom.comp (PolynomialPresentation.frobenius p k C σ x n).toRingHom =
      (FiniteField.frobeniusAlgHom k C).toRingHom.comp (reductionDP p k C σ x n).toRingHom := by
  have he := EnvelopeFunctor.endomorphism_natural B P J δ (algebraMap B P) I
    (Ideal.map_le_iff_le_comap.mp (PolynomialPresentation.base_le p k C σ x n)) (DividedPowers.DPMorphism.id δ)
    (PolynomialPresentation.polynomialFrobenius p k σ n).toRingHom (PolynomialPresentation.polynomialFrobenius_base p k σ n)
    (PolynomialPresentation.polynomialFrobenius_preserves_kernel p k C σ x n) (residueTarget p k C σ x n)
    (DividedPower.Transfer.botMap (FiniteField.frobeniusAlgHom k C).toRingHom)
    (PolynomialPresentation.polynomialFrobenius_reduction p k C σ x n).symm
  exact congrArg (fun g : DividedPowers.DPMorphism ε (dividedPowersBot C) => g.toRingHom) he

def quotientReductionDP : DividedPowers.DPMorphism ε (dividedPowersBot C) :=
  DividedPower.Transfer.mapToBot ε ((e).toRingHom.comp (Ideal.Quotient.mk IE)) (by
    intro a ha
    change e (Ideal.Quotient.mk IE a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])

theorem reduction_eq_quotient :
    (reductionDP p k C σ x n).toRingHom = (e).toRingHom.comp (Ideal.Quotient.mk IE) := by
  have he : quotientReductionDP p k C σ x n hx = reductionDP p k C σ x n := by
    apply DividedPower.PowerEnvelope.lift_unique B P J δ (algebraMap B P) I (residueTarget p k C σ x n)
    apply RingHom.ext
    exact quotientEquiv_polynomial p k C σ x n hx
  exact (congrArg (fun g : DividedPowers.DPMorphism ε (dividedPowersBot C) => g.toRingHom) he).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CrystallineFrame
