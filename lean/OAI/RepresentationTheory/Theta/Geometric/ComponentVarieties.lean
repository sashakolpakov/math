import OAI.RepresentationTheory.Theta.Geometric.Projective.BaseChange
import OAI.RepresentationTheory.Theta.Geometric.Components

/-! # Component Varieties -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The supplied arithmetic closed projective embeddings construct actual
integral smooth projective varieties for the native complex PEL components.
All comparisons retain their scheme maps over the complex base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace ComponentVarieties.RelativeProjective

def coefficientOverIso {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) :
    Over.mk (Projective.Map.RelativeProjective.projectiveSpaceToBase S n) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n) :=
  Over.isoMk (Projective.BaseChange.RelativeProjective.projectiveBaseChangeIso f n) (Projective.BaseChange.RelativeProjective.coefficient_isPullback f n).isoPullback_hom_snd

def projectiveOverComplexIso {B : Scheme} (c : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (n : ℕ) :
    (Over.pullback c).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver B n) ≅
      Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := by
  refine ((Over.pullbackComp c B.toSpecΓ).app
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(B, ⊤) n)).symm ≪≫ ?_
  let f := Classical.choose (Spec.map_surjective (c ≫ B.toSpecΓ))
  have hf : Spec.map f = c ≫ B.toSpecΓ := Classical.choose_spec (Spec.map_surjective (c ≫ B.toSpecΓ))
  let F : (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec Γ(B, ⊤)) →
      (Over (Spec Γ(B, ⊤)) ⥤ Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) := fun a => Over.pullback a
  change (F (c ≫ B.toSpecΓ)).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(B, ⊤) n) ≅ _
  rw [← hf]
  exact (coefficientOverIso f.hom n).symm

def complexProjectivePresentation {B : Scheme} {X : Over B}
    (P : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) (c : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) :
    AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation ((Over.pullback c).obj X).left
      ((Over.pullback c).obj X).hom where
  ambientDimension := P.dimension
  embedding := ((Over.pullback c).map P.embedding ≫ (projectiveOverComplexIso c P.dimension).hom).left
  closedImmersion := by
    have : IsClosedImmersion ((Over.pullback c).map P.embedding).left :=
      MorphismProperty.overPullbackMap c P.embedding P.closedImmersion
    have : IsIso (projectiveOverComplexIso c P.dimension).hom.left :=
      ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso (projectiveOverComplexIso c P.dimension)).isIso_hom
    change IsClosedImmersion (((Over.pullback c).map P.embedding).left ≫
      (projectiveOverComplexIso c P.dimension).hom.left)
    infer_instance
  over_base := ((Over.pullback c).map P.embedding ≫ (projectiveOverComplexIso c P.dimension).hom).w

end ComponentVarieties.RelativeProjective

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.component_projective (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount) :
    Nonempty (AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (D.componentComplex j).left
      (D.componentComplex j).hom) := by
  let P := Classical.choice (hg.componentGeometry j).2.2.1
  let C := (Over.pullback D.pel.complexPoint).obj (D.pel.components.S j)
  let e : C ≅ D.componentComplex j :=
    (Over.pullbackComp D.pel.complexGenericPoint D.pel.generic).app (D.pel.components.S j)
  have hp : Nonempty (AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation C.left C.hom) :=
    ⟨ComponentVarieties.RelativeProjective.complexProjectivePresentation P D.pel.complexPoint⟩
  exact (AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation.nonempty_iff_of_iso
    ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e.symm) e.inv.w).mpr hp

def Data.ActiveHeckeThetaData.componentVariety (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  ⟨{ carrier := (D.componentComplex j).left
     structureMap := (D.componentComplex j).hom
     projective := Classical.choice (D.component_projective hg j)
     smooth := (D.component_smooth_proper_connected hg j).1 },
    D.component_integral hg j⟩

def Data.ActiveHeckeThetaData.componentVarietyIso (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount) :
    (D.componentVariety hg j).toOver ≅ D.componentComplex j := Iso.refl _

end

end OAI.RepresentationTheory.Theta.Geometric
