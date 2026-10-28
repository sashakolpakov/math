import OAI.AlgebraicGeometry.DivisorClass.Chern.UniformizerSupport
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension

/-! # Scheme Uniformizer Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SchemeUniformizerSupport

noncomputable section

/-!
# ChernClass: the actual section parameter defines the point closure nearby

The affine prime is the original scheme point's prime. Transport the
uniformizer through its genuine stalk localization, clear denominators,
and translate the resulting support equality back to the original scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme}

/-- Membership of the affine prime is the actual failure of a section
germ to be a unit at that scheme point. -/
theorem mem_affinePointPrime_iff {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) (p : Γ(X, U)) :
    p ∈ (hU.primeIdealOf x).asIdeal ↔ ¬ IsUnit (X.presheaf.germ U x.val x.property p) := by
  rw [hU.primeIdealOf_eq_map_closedPoint]
  rfl

/-- The point closure has its literal prime-specialization description
in the actual affine spectrum chart. -/
theorem affinePoint_mem_closure_iff {U : X.Opens} (hU : IsAffineOpen U) (x y : U) :
    y.val ∈ closure ({x.val} : Set X) ↔ (hU.primeIdealOf x).asIdeal ≤ (hU.primeIdealOf y).asIdeal := by
  have hpre : hU.fromSpec ⁻¹' ({x.val} : Set X) = {hU.primeIdealOf x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [hU.fromSpec_primeIdealOf, h]
    · rintro rfl
      exact hU.fromSpec_primeIdealOf x
  have hcl := hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    hU.fromSpec.continuous ({x.val} : Set X)
  rw [hpre, PrimeSpectrum.closure_singleton] at hcl
  have hm := Set.ext_iff.mp hcl (hU.primeIdealOf y)
  rw [Set.mem_preimage, hU.fromSpec_primeIdealOf] at hm
  exact hm

/-- On a genuine principal neighborhood, the original regular section's
nonunit locus is exactly the closure of the original codimension-one point. -/
theorem smooth_uniformizer_section_support_neighborhood [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hxU : x ∈ U) (hx : Order.coheight x = 1)
    (p : Γ(X, U)) (hp : Irreducible (X.presheaf.germ U x hxU p)) :
    ∃ b : Γ(X, U), IsUnit (X.presheaf.germ U x hxU b) ∧
      ∀ y : U, IsUnit (X.presheaf.germ U y.val y.property b) →
        (¬ IsUnit (X.presheaf.germ U y.val y.property p) ↔ y.val ∈ closure ({x} : Set X)) := by
  let P := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let := hU.isLocalization_stalk ⟨x, hxU⟩
  let : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    HodgeConjecture.DegreeTwo.SmoothDVR.Constructions.smoothScheme_stalk_isDiscreteValuationRing f x hx
  let e : (X.presheaf.stalk x) ≃ₐ[Γ(X, U)] Localization.AtPrime P :=
    IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk x) (Localization.AtPrime P)
  let : IsDomain (Localization.AtPrime P) := Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  let : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hp' := hp.map e.toMulEquiv
  change Irreducible (e (algebraMap Γ(X, U) (X.presheaf.stalk x) p)) at hp'
  rw [e.commutes] at hp'
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨b, hb, hmodel⟩ := UniformizerSupport.uniformizer_prime_support_neighborhood P p hp'
  refine ⟨b, ?_, ?_⟩
  · exact IsLocalization.map_units (X.presheaf.stalk x) (⟨b, hb⟩ : P.primeCompl)
  · intro y hy
    rw [← mem_affinePointPrime_iff hU y p, affinePoint_mem_closure_iff hU ⟨x, hxU⟩ y]
    exact hmodel (hU.primeIdealOf y).asIdeal inferInstance
      (fun hb => (mem_affinePointPrime_iff hU y b).mp hb hy)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SchemeUniformizerSupport
