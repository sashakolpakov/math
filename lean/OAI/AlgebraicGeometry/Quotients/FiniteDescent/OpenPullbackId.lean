import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseOpen
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict

/-! # Open Pullback Id -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackId

noncomputable section

/-! Restricting the geometric pullback map to an open subscheme preserves actual sections. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

namespace Construction.OpenPullbackSections

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)

private theorem on_image (s : Γ(M.restrict U.ι, ⊤)) :
    ((OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).hom.app M).app ⊤
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (f ∣_ U) (M.restrict U.ι) ⊤ s) =
    ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
        (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U.ι ''ᵁ ⊤) s) := by
  have h := congrArg (fun a => a.app ⊤) (OpenPullbackIs.Construction.OpenPullbackSquare.unit_square f U M)
  simp only [Scheme.Modules.Hom.comp_app, OpenPullbackIs.Construction.OpenPullbackSquare.restrict_map_app,
    OpenPullbackIs.Construction.OpenPullbackSquare.map_app, Scheme.Modules.pushforward_map_app] at h
  exact (ConcreteCategory.congr_hom h s).symm

private theorem mapped_three_id {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {U V W : C} (a : U ⟶ V) (b : V ⟶ W) (c : W ⟶ U)
    (h : a ≫ b ≫ c = 𝟙 U) : P.map a ≫ P.map b ≫ P.map c = 𝟙 (P.obj U) := by
  rw [← P.map_comp, ← P.map_comp, h, P.map_id]

theorem normalization (s : Γ(M, U)) :
    (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)).hom
      (((OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).hom.app M).app ⊤
        (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (f ∣_ U) (M.restrict U.ι) ⊤
          ((SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).inv s))) = PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s := by
  rw [on_image]
  let P := (Scheme.Modules.pullback f).obj M
  let e := (eqToHom U.ι_image_top).op
  have hn := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val e s
  change PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U.ι ''ᵁ ⊤)
      ((SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).inv s) =
    P.presheaf.map ((TopologicalSpace.Opens.map f.base).op.map e)
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s) at hn
  rw [hn]
  change P.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top.symm).op
    (P.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
      (P.presheaf.map ((TopologicalSpace.Opens.map f.base).op.map e)
        (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s))) = _
  have h := mapped_three_id P.presheaf ((TopologicalSpace.Opens.map f.base).op.map e)
    (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
    (eqToHom (f ⁻¹ᵁ U).ι_image_top.symm).op (Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom h (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s)

end Construction.OpenPullbackSections

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackId
