import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange
import Mathlib.RingTheory.RingHom.Etale

/-! # Isomorphic Blowup Equiv -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupEquiv.Construction

noncomputable section

/-! Transport isomorphism of actual affine blowups through ring equivalences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineBlowup_isIso_of_comap_equiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal S) [IsIso (ReesGrading.Construction.affineBlowupToSpec I)] :
    IsIso (ReesGrading.Construction.affineBlowupToSpec (I.comap e.toRingHom)) := by
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  let : Algebra.Etale S R := RingHom.Etale.of_bijective e.symm.bijective
  have hpb := Blowup.FlatBaseChange.Construction.affineBlowup_flat_isPullback (S := R) I
  have h : IsIso (ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap S R))) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) hpb inferInstance
  have he : I.map (algebraMap S R) = I.comap e.toRingHom := Ideal.map_symm e
  exact he ▸ h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupEquiv.Construction
