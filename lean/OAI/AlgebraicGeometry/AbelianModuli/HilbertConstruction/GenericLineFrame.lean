import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Generic Line Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenericLineFrame

noncomputable section

/-! An actual generic line sheaf has a structure-module frame on a nonempty affine open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

def imageRestrictionIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : Y.Opens) (M : X.Modules) :
    M.restrict (f ''ᵁ W).ι ≅ ((M.restrict f).restrict W.ι).restrict (f.isoImage W).inv :=
  (restrictFunctorCongr (f.isoImage_inv_ι W).symm).app M ≪≫
    (restrictFunctorComp (f.isoImage W).inv (W.ι ≫ f)).app M ≪≫
      (restrictFunctor (f.isoImage W).inv).mapIso ((restrictFunctorComp W.ι f).app M)

theorem exists_generic_line_frame
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) [Nonempty U]
    (L : Line.Bundles.LineBundle U.toScheme) (e : M.restrict U.ι ≅ L.sheaf) :
    ∃ V : X.Opens, V ≤ U ∧ Nonempty V ∧ IsAffineOpen V ∧
      Nonempty (M.restrict V.ι ≅ Line.Bundles.structureModule V.toScheme) := by
  obtain ⟨W, hxW, hW, ⟨b⟩⟩ := L.exists_affine_frame (Classical.arbitrary U)
  let V : X.Opens := U.ι ''ᵁ W
  have hV : Nonempty V := ⟨⟨U.ι (Classical.arbitrary U), _, hxW, rfl⟩⟩
  let b' : (M.restrict U.ι).restrict W.ι ≅ Line.Bundles.structureModule W.toScheme :=
    (restrictFunctor W.ι).mapIso e ≪≫
      (restrictFunctorIsoPullback W.ι).app L.sheaf ≪≫ b
  exact ⟨V, U.ι_image_le W, hV, hW.image_of_isOpenImmersion U.ι,
    ⟨imageRestrictionIso U.ι W M ≪≫
      (restrictFunctor (U.ι.isoImage W).inv).mapIso b' ≪≫
        restrictUnitIso (U.ι.isoImage W).inv⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenericLineFrame
