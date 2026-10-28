import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Descent

/-! # Complex Smooth Proper Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexSmoothProperDescent

noncomputable section

/-! Smoothness and properness descend from the actual complex fiber
along a specified embedding of the ground field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem smooth_proper_of_complex_baseChange {K : Type} [Field K]
    (κ : K →+* ℂ) (X : Over (Spec (.of K)))
    (hs : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X).hom)
    (hp : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X).hom) :
    Smooth X.hom ∧ IsProper X.hom := by
  let : Algebra K ℂ := κ.toAlgebra
  let b := Spec.map (CommRingCat.ofHom κ)
  have : Flat b := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap K ℂ)))
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Surjective b := ⟨fun x => ⟨IsLocalRing.closedPoint ℂ, Subsingleton.elim _ x⟩⟩
  have : QuasiCompact b := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom κ)))
  have : Smooth (pullback.snd X.hom b) := hs
  have : IsProper (pullback.snd X.hom b) := hp
  refine ⟨?_, Descent.proper_of_faithfully_flat_cartesian (IsPullback.of_hasPullback X.hom b).flip⟩
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := X.hom) (g := b) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hs

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexSmoothProperDescent
