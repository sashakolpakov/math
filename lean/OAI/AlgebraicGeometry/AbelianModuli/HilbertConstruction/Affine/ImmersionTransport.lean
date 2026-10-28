import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenImmersionIsomorphism

/-! # Immersion Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ImmersionTransport

noncomputable section

/-! Affine open immersions transport across commuting ring isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isOpenImmersion_SpecMap_of_conjugate
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (ψ : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (w : ∀ x, eB (φ x) = ψ (eA x))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ)) := by
  have : IsIso (CommRingCat.ofHom eA.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr eA.bijective
  have : IsIso (CommRingCat.ofHom eB.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr eB.bijective
  have hw : Spec.map (CommRingCat.ofHom eB.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom eA.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext w)
  have hc : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom eB.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ)) := inferInstance
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom eA.toRingHom)) :=
    (congrArg (fun f => IsOpenImmersion f) hw).mp hc
  exact IsOpenImmersion.of_comp (Spec.map (CommRingCat.ofHom ψ))
    (Spec.map (CommRingCat.ofHom eA.toRingHom))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ImmersionTransport
