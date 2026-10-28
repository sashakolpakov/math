import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageGroup
import OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoGroupFlat
import OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantOpenGroupIso

/-! # Group Monomorphism Closed -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupMonomorphismClosed

noncomputable section

/-! Finite-type monomorphisms of algebraic groups over an algebraically
closed field are closed immersions, including nonreduced groups. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B]
  [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]
  (f : A ⟶ B) [IsMonHom f] [Mono f.left] [QuasiCompact f.left]

theorem groupMonomorphism_imageFactor_isIso : IsIso (OverSchemeImage.Construction.overSchemeImageFactor f).left := by
  have : LocallyOfFiniteType (OverSchemeImage.Construction.overSchemeImage f).hom :=
    inferInstanceAs (LocallyOfFiniteType (f.left.imageι ≫ B.hom))
  have : Mono ((OverSchemeImage.Construction.overSchemeImageFactor f).left ≫ (OverSchemeImage.Construction.overSchemeImageInclusion f).left) := by
    change Mono (f.left.toImage ≫ f.left.imageι)
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : Mono (OverSchemeImage.Construction.overSchemeImageFactor f).left := mono_of_mono _ (OverSchemeImage.Construction.overSchemeImageInclusion f).left
  have : IsOpenImmersion (OverSchemeImage.Construction.overSchemeImageFactor f).left :=
    DominantMonoGroupFlat.Construction.dominantMono_groupHom_isOpenImmersion (OverSchemeImage.Construction.overSchemeImageFactor f)
  exact DominantOpenGroupIso.Construction.dominantOpen_groupHom_isIso (OverSchemeImage.Construction.overSchemeImageFactor f)

theorem groupMonomorphism_isClosedImmersion : IsClosedImmersion f.left := by
  have := groupMonomorphism_imageFactor_isIso f
  have h : IsClosedImmersion ((OverSchemeImage.Construction.overSchemeImageFactor f).left ≫ (OverSchemeImage.Construction.overSchemeImageInclusion f).left) :=
    inferInstance
  have he := congrArg Over.Hom.left (OverSchemeImage.Construction.overSchemeImageFactor_inclusion f)
  exact he ▸ h

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupMonomorphismClosed
