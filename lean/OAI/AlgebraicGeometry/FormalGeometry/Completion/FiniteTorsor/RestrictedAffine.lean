import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.AffineCover
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.RestrictionSlice
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.FiniteSheafRepresentation

/-! # Restricted Affine -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: finite étale representatives after restriction to any affine site object

An actual torsor on an arbitrary base restricts to a representable finite
étale sheaf on every affine weakly étale scheme over that base.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ℓ n : ℕ}
  (E : App.Construction.FiniteCoefficientExtension ℓ n X)
  (b : Spec (CommRingCat.of R) ⟶ X) (hb : WeaklyEtale b)

/-- A restricted actual torsor admits an affine faithfully flat ring trivialization. -/
theorem App.Construction.FiniteCoefficientExtension.exists_affine_ring_trivialization_over :
    ∃ (S : CommRingCat.{u}) (f : R →+* S)
      (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f))),
      f.FaithfullyFlat ∧ Nonempty (E.Fiber ((ProEtale.EtaleRestriction.Construction.proEtCompose b hb).obj (Affine.CoverObject.Construction.affineCoverObject f hf))) := by
  have := hb
  let U : X.ProEt := Scheme.ProEt.mk b
  have : IsAffine U.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  obtain ⟨T, g, hT, hg, ⟨s⟩⟩ := E.exists_affine_cover_lift U
  have : IsAffine T.left := hT
  have : Surjective g.left := hg
  have : WeaklyEtale g.left := ProEtale.SingleCover.Construction.proEtaleMorphism_weaklyEtale g
  let f : CommRingCat.of R ⟶ Γ(T.left, ⊤) := Spec.preimage (T.left.isoSpec.inv ≫ g.left)
  have hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f.hom)) := by
    change WeaklyEtale (Spec.map f)
    rw [show Spec.map f = T.left.isoSpec.inv ≫ g.left from Spec.map_preimage _]
    infer_instance
  have hsurj : Surjective (Spec.map f) := by
    rw [show Spec.map f = T.left.isoSpec.inv ≫ g.left from Spec.map_preimage _]
    infer_instance
  have hflat : f.hom.FaithfullyFlat :=
    (flat_and_surjective_SpecMap_iff f).mp ⟨hf.flat, hsurj⟩
  let e : (ProEtale.EtaleRestriction.Construction.proEtCompose b hb).obj (Affine.CoverObject.Construction.affineCoverObject f.hom hf) ≅ T :=
    MorphismProperty.Over.isoMk T.left.isoSpec.symm (by
      change T.left.isoSpec.inv ≫ T.hom = Spec.map f ≫ b
      rw [show Spec.map f = T.left.isoSpec.inv ≫ g.left from Spec.map_preimage _]
      rw [Category.assoc]
      exact congrArg (fun k => T.left.isoSpec.inv ≫ k) (MorphismProperty.Over.w g).symm)
  exact ⟨Γ(T.left, ⊤), f.hom, hf, hflat, ⟨E.restrict e.hom s⟩⟩

/-- The torsor restricted to any affine weakly étale base is an actual finite étale scheme. -/
theorem App.Construction.FiniteCoefficientExtension.exists_finiteEtale_representative_restricted_affine [NeZero (ℓ ^ n)] :
    ∃ T : (Spec (CommRingCat.of R)).ProEt,
      IsFinite T.hom ∧ Etale T.hom ∧
        Nonempty (((ProEtale.EtaleRestriction.Construction.proEtCompose b hb).op ⋙ E.fiberPresheaf).RepresentableBy T) := by
  obtain ⟨S, f, hf, hflat, ⟨s⟩⟩ := E.exists_affine_ring_trivialization_over b hb
  let F := (ProEtale.EtaleRestriction.Construction.proEtSheafRestriction b hb (Type (u + 1))).obj E.fiberSheaf
  exact Affine.FiniteSheafRepresentation.Construction.exists_affineSheaf_finiteEtale_representative.{u, u + 1} f hf ℓ n F
    (E.restrictedLocalRepresentative b hb (Affine.CoverObject.Construction.affineCoverObject f hf) s) hflat

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
