import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange

/-! # Blowup Smooth Equiv -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupSmoothEquiv.Construction

noncomputable section

/-! Smoothness of actual affine blowups under scalar-compatible ring equivalences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineBlowup_smooth_of_comap_algEquiv
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (e : R ≃ₐ[k] S) (I : Ideal S)
    [Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)))] :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (I.comap e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  let : Algebra.Etale S R := RingHom.Etale.of_bijective e.symm.bijective
  let : Etale (ReesMap.Construction.affineBlowupMap I e.symm.toRingHom) := Blowup.FlatBaseChange.Construction.affineBlowupMap_etale I
  have hg : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k S)) =
      Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (algebraMap k S))) = _
    exact congrArg (fun φ : k →+* R => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext e.symm.commutes)
  have h : Smooth (ReesMap.Construction.affineBlowupMap I e.symm.toRingHom ≫
      (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)))) := inferInstance
  rw [← Category.assoc, Blowup.BaseOpen.Construction.affineBlowupMap_over, Category.assoc, hg] at h
  have he : I.map e.symm.toRingHom = I.comap e.toRingHom := Ideal.map_symm e.toRingEquiv
  exact he ▸ h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupSmoothEquiv.Construction
