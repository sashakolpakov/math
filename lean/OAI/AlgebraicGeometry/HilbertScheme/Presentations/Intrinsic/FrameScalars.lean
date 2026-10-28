import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameScalarRescaling
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitScalar

/-! # Frame Scalars -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FrameScalars

noncomputable section

/-! Native scalar automorphisms and Presentations scalar values agree exactly,
including the inverse transition convention of projective twist frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}}

theorem nativeUnitEndomorphism_value (r : Γ(X, ⊤)) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection r) = r := by
  change 1 * X.presheaf.map (homOfLE (le_refl (⊤ : X.Opens))).op r = r
  rw [one_mul]
  change X.presheaf.map (𝟙 _) r = r
  rw [X.presheaf.map_id]
  rfl

theorem nativeUnitAutomorphism_eq (c : Γ(X, ⊤)ˣ) :
    SheafCohomology.Projective.UnitScalar.unitAutomorphismOfTopUnit c = FrameScalarRescaling.structureScalarAutomorphism c := by
  apply Iso.ext
  apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X
  rw [FrameScalarRescaling.structureScalarAutomorphism_hom_value]
  exact nativeUnitEndomorphism_value (c : Γ(X, ⊤))

theorem frameTransitionValue_of_native_transition {M : X.Modules}
    (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (c : Γ(X, ⊤)ˣ)
    (h : e.hom = f.hom ≫ SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (c : Γ(X, ⊤))) :
    FrameTransitionCocycles.frameTransitionValue e f = ((c⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) := by
  have hc : e.hom = f.hom ≫ (FrameScalarRescaling.structureScalarAutomorphism c).hom := by
    change e.hom = f.hom ≫ (SheafCohomology.Projective.UnitScalar.unitAutomorphismOfTopUnit c).hom at h
    rwa [nativeUnitAutomorphism_eq] at h
  have he : e.inv ≫ f.hom = (FrameScalarRescaling.structureScalarAutomorphism c).inv := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc, hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold FrameTransitionCocycles.frameTransitionValue
  rw [he, FrameScalarRescaling.structureScalarAutomorphism_inv_value]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FrameScalars
