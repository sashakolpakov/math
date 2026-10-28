import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CrystallineFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cover

/-! # Crystalline Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CrystallineCover

noncomputable section

/-!
# IntegralComparison: finite polynomial frames receive every affine crystalline object

Lift a chosen algebra generating family into the given thickening. Its
nilpotence bound factors the Witt base through a finite quotient, and
the proved envelope property gives an actual morphism to the frame.
Finite type supplies a finite generating family unconditionally.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (C σ : Type u) [CommRing C] [Algebra k C] (x : σ → C)
  (U : Witt.Crystalline.CrystallineObject p k (Crystalline.Presentation.affineScheme k C))

local notation "W" => WittVector p k
local notation "JW" => Ideal.span {(p : W)}
local notation "δW" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cover.levelBound p k C U
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k N
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.ideal p k N
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.dividedPowers p k N
local notation "P" => MvPolynomial σ B
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.kernel p k C σ x N
local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.dividedPowers p k C σ x N
local notation "c" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cover.closedRingMap p k C U

omit [Fintype k] in
theorem base_kills : JW ^ (N + 1) ≤ RingHom.ker U.base := by
  rw [Ideal.span_singleton_pow, Ideal.span_le]
  rintro a (rfl : a = _)
  change U.base ((p : W) ^ (N + 1)) = 0
  rw [map_pow, map_natCast, pow_succ, Crystalline.Cover.prime_pow_bound, zero_mul]

def truncatedBase : B →+* U.ring := Ideal.Quotient.lift _ U.base (base_kills p k C U)

omit [Fintype k] in
theorem truncatedBase_quotient :
    (truncatedBase p k C U).comp (Truncated.Witt.quotient p k N) = U.base := by
  apply RingHom.ext
  intro w
  rfl

omit [Fintype k] in
theorem truncatedBase_isDPMorphism : DividedPowers.IsDPMorphism δ U.dividedPowers (truncatedBase p k C U) := by
  apply DividedPowers.IsDPMorphism.of_comp δW δ U.dividedPowers (Truncated.Witt.quotient p k N)
    (truncatedBase p k C U) rfl (Truncated.Witt.quotient_isDPMorphism p k N)
  rw [truncatedBase_quotient]
  exact U.baseCompatible

theorem truncatedBase_reduction :
    (Ideal.Quotient.mk U.ideal).comp (truncatedBase p k C U) =
      (c).comp (PolynomialPresentation.coefficientReduction p k C N) := by
  apply RingHom.ext
  intro b
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact (DFunLike.congr_fun (Crystalline.Cover.closedRingMap_coefficients p k C U) w).symm

def polynomialMap : P →+* U.ring :=
  MvPolynomial.eval₂Hom (truncatedBase p k C U)
    (fun i => Crystalline.Cover.variableLift p k C U (x i))

theorem polynomialMap_reduction :
    (Ideal.Quotient.mk U.ideal).comp (polynomialMap p k C σ x U) =
      (c).comp (PolynomialPresentation.reduction p k C σ x N) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, polynomialMap, PolynomialPresentation.reduction,
      MvPolynomial.eval₂Hom_C]
    exact DFunLike.congr_fun (truncatedBase_reduction p k C U) b
  · intro i
    simp only [RingHom.comp_apply, polynomialMap, PolynomialPresentation.reduction,
      MvPolynomial.eval₂Hom_X']
    exact Crystalline.Cover.variableLift_reduction p k C U (x i)

omit [Fintype k] in
theorem polynomialMap_base :
    (polynomialMap p k C σ x U).comp (algebraMap B P) = truncatedBase p k C U := by
  apply RingHom.ext
  intro b
  exact MvPolynomial.eval₂Hom_C _ _ b

theorem polynomialMap_mapsKernel : I ≤ U.ideal.comap (polynomialMap p k C σ x U) := by
  intro a ha
  change polynomialMap p k C σ x U a ∈ U.ideal
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have he := DFunLike.congr_fun (polynomialMap_reduction p k C σ x U) a
  change Ideal.Quotient.mk U.ideal (polynomialMap p k C σ x U a) =
    c (PolynomialPresentation.reduction p k C σ x N a) at he
  rw [he, show PolynomialPresentation.reduction p k C σ x N a = 0 from ha, map_zero]

def target : DividedPower.PowerEnvelope.Target B P J δ (algebraMap B P) I where
  ring := U.ring
  ideal := U.ideal
  dividedPowers := U.dividedPowers
  fromBase := polynomialMap p k C σ x U
  mapsIdeal := polynomialMap_mapsKernel p k C σ x U
  baseCompatible := by
    rw [polynomialMap_base]
    exact truncatedBase_isDPMorphism p k C U

def envelopeMap : DividedPowers.DPMorphism ε U.dividedPowers :=
  DividedPower.PowerEnvelope.lift B P J δ (algebraMap B P) I (target p k C σ x U)

theorem envelopeMap_polynomial :
    (envelopeMap p k C σ x U).toRingHom.comp (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) I) =
      polynomialMap p k C σ x U :=
  DividedPower.PowerEnvelope.lift_fromBase B P J δ (algebraMap B P) I (target p k C σ x U)

theorem envelopeMap_base :
    (envelopeMap p k C σ x U).toRingHom.comp (PolynomialPresentation.base p k C σ x N) = U.base := by
  change (envelopeMap p k C σ x U).toRingHom.comp
    (((DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) I).comp (algebraMap B P)).comp
      (Truncated.Witt.quotient p k N)) = U.base
  rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, envelopeMap_polynomial,
    polynomialMap_base, truncatedBase_quotient]

theorem envelopeMap_reduction :
    (Ideal.Quotient.mk U.ideal).comp (envelopeMap p k C σ x U).toRingHom =
      (c).comp (CrystallineFrame.reductionDP p k C σ x N).toRingHom := by
  let q := DividedPower.Transfer.mapToBot U.dividedPowers (Ideal.Quotient.mk U.ideal)
    (fun _a ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  let V := DividedPower.PowerEnvelope.postcomposeTarget B P J δ (algebraMap B P) I (target p k C σ x U)
    (dividedPowersBot (U.ring ⧸ U.ideal)) q
  let g := DividedPower.Transfer.botMap c
  have hleft : q.comp (envelopeMap p k C σ x U) = DividedPower.PowerEnvelope.lift B P J δ (algebraMap B P) I V :=
    DividedPower.PowerEnvelope.lift_postcompose B P J δ (algebraMap B P) I (target p k C σ x U)
      (dividedPowersBot (U.ring ⧸ U.ideal)) q
  have hright : g.comp (CrystallineFrame.reductionDP p k C σ x N) =
      DividedPower.PowerEnvelope.lift B P J δ (algebraMap B P) I V := by
    apply DividedPower.PowerEnvelope.lift_unique B P J δ (algebraMap B P) I V
    change (c).comp ((CrystallineFrame.reductionDP p k C σ x N).toRingHom.comp
      (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) I)) =
      (Ideal.Quotient.mk U.ideal).comp (polynomialMap p k C σ x U)
    rw [CrystallineFrame.reduction_polynomial]
    exact (polynomialMap_reduction p k C σ x U).symm
  exact congrArg (fun g : DividedPowers.DPMorphism ε (dividedPowersBot (U.ring ⧸ U.ideal)) =>
    g.toRingHom) (hleft.trans hright.symm)

variable (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] C))

local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CrystallineFrame.object p k C σ x N hx
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.quotientEquiv p k C σ x N hx

theorem quotientMap_closed :
    (Crystalline.Site.AffineThickening.quotientMap U V (envelopeMap p k C σ x U)).comp
      (e).symm.toRingHom = c := by
  apply RingHom.ext
  intro a
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective ((e).symm a)
  change Crystalline.Site.AffineThickening.quotientMap U V (envelopeMap p k C σ x U)
    ((e).symm a) = c a
  rw [← hd]
  change Ideal.Quotient.mk U.ideal (envelopeMap p k C σ x U d) = c a
  have hr := DFunLike.congr_fun (envelopeMap_reduction p k C σ x U) d
  change Ideal.Quotient.mk U.ideal (envelopeMap p k C σ x U d) =
    c (CrystallineFrame.reductionDP p k C σ x N d) at hr
  rw [hr]
  change c ((CrystallineFrame.reductionDP p k C σ x N).toRingHom d) = c a
  rw [DFunLike.congr_fun (CrystallineFrame.reduction_eq_quotient p k C σ x N hx) d]
  change c (e (Ideal.Quotient.mk _ d)) = c a
  rw [hd, RingEquiv.apply_symm_apply]

/-- The map to the finite polynomial frame is a morphism of the original site. -/
def presentationMorphism : U ⟶ V where
  ringMap := envelopeMap p k C σ x U
  overBase := envelopeMap_base p k C σ x U
  overX := by
    change Spec.map (CommRingCat.ofHom
      (Crystalline.Site.AffineThickening.quotientMap U V (envelopeMap p k C σ x U))) ≫
      Spec.map (CommRingCat.ofHom (e).symm.toRingHom) = U.openMap
    rw [← Spec.map_comp, ← Crystalline.Cover.closedRingMap_spec p k C U]
    exact congrArg (fun g : C →+* U.ring ⧸ U.ideal => Spec.map (CommRingCat.ofHom g))
      (quotientMap_closed p k C σ x U hx)

include U in
/-- Every affine crystalline object over a finite-type algebra maps to a finite polynomial frame. -/
theorem exists_finite_frame [Algebra.FiniteType k C] :
    ∃ (σ : Type u) (_ : Fintype σ) (x : σ → C)
      (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] C)) (n : ℕ),
      Nonempty (U ⟶ CrystallineFrame.object p k C σ x n hx) := by
  obtain ⟨σ, hσ, x, hx⟩ := Generators.exists_generators k C
  exact ⟨σ, hσ, x, hx, N, ⟨presentationMorphism p k C σ x U hx⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CrystallineCover
