import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

/-! # Open Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.OpenCoordinates

noncomputable section

/-! Ambient local-frame coordinates agree with the actual coordinates
on the open subscheme, through its regular-section restriction map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} (M : X.Modules)

theorem transportFrame_section {U V : X.Opens} (h : U = V)
    (e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) (m : Γ(M, V)) :
    e (M.presheaf.map (eqToHom h).op m) =
      X.presheaf.map (eqToHom h).op (DivisorClass.Chern.FramesFrame.Construction.transportFrame M h e m) := by
  subst V
  simp only [eqToHom_refl, op_id]
  rw [M.presheaf.map_id, X.presheaf.map_id]
  rfl

theorem frameOnOpen_subscheme (U : X.Opens)
    (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (V : X.Opens) (hV : V ≤ U) (m : Γ(M, V)) :
    e.hom.app (U.ι ⁻¹ᵁ V) (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m) =
      U.ι.app V (DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U e V hV m) :=
  transportFrame_section M (DivisorClass.Chern.FramesFrame.Construction.image_preimage_subopen U hV) (DivisorClass.Chern.FramesFrame.Construction.frameOnImage M U e (U.ι ⁻¹ᵁ V)) m

theorem openInclusion_app_injective (U V : X.Opens) (hV : V ≤ U) :
    Function.Injective (U.ι.app V) := by
  change Function.Injective (X.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op)
  have he : homOfLE (U.ι.image_preimage_le V) = eqToHom (DivisorClass.Chern.FramesFrame.Construction.image_preimage_subopen U hV) :=
    Subsingleton.elim _ _
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom (DivisorClass.Chern.FramesFrame.Construction.image_preimage_subopen U hV)).op)).injective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.OpenCoordinates
