import OAI.RepresentationTheory.Theta.Geometric.ComponentProjectorMaps
import OAI.RepresentationTheory.Theta.Geometric.Rational.FormsPullback
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants

/-! # Ball Forms Projector -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original ball projector on Albanese forms restricts to the
identity on its component and to zero on every other component. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem BallFormsProjector.modelComponent_projector (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (i j : Fin D.componentCount) :
    let e := @asIso _ _ _ _ D.componentAssembly hg.decomposition
    let m := D.components.totalMap e ≫ (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison D.components.A).inv
    (D.inclusion i ≫ m) ≫ Geometry.productCoordinateIdempotent D.components.A j =
      if i = j then D.inclusion i ≫ m else 1 := by
  dsimp only
  let e := @asIso _ _ _ _ D.componentAssembly hg.decomposition
  have hi : Sigma.ι D.components.S i ≫ e.hom = D.inclusion i := by
    simp only [e, asIso_hom, AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc]
  have hm : D.inclusion i ≫ D.components.totalMap e = D.components.componentProductMap i := by
    rw [← hi]
    simp only [AlgebraicGeometry.PELModuli.IntegralModel.Components.ComponentAlbaneseData.totalMap, Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_comp_desc]
  change (D.inclusion i ≫ (D.components.totalMap e ≫ (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison D.components.A).inv)) ≫
    Geometry.productCoordinateIdempotent D.components.A j =
    if i = j then D.inclusion i ≫ (D.components.totalMap e ≫ (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison D.components.A).inv) else 1
  simp only [← Category.assoc, hm]
  exact ComponentProjectorMaps.componentProductMap_projector D.components i j

variable {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

local instance Data.ActiveHeckeThetaData.ballProjectorGroup : GrpObj D.pel.complexAlbanese.X := D.pel.complexAlbanese.grp
local instance Data.ActiveHeckeThetaData.ballProjectorComm : IsCommMonObj D.pel.complexAlbanese.X := D.pel.complexAlbanese.comm

def Data.ActiveHeckeThetaData.ballAlbaneseProjector (j : Fin D.pel.componentCount) : D.pel.complexAlbanese.X ⟶ D.pel.complexAlbanese.X :=
  (Over.pullback D.pel.complexGenericPoint).map
    ((Over.pullback D.pel.generic).map (Geometry.productCoordinateIdempotent D.pel.components.A j))

def Data.ActiveHeckeThetaData.ballFormsProjector (j : Fin D.pel.componentCount) : Module.End ℂ D.pel.OneFormsA :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.ballAlbaneseProjector j)

theorem Data.ActiveHeckeThetaData.componentAlbanese_projector (hg : D.pel.HasIntegralModelGeometry) (i j : Fin D.pel.componentCount) :
    (D.componentComplexInclusion i ≫ D.pel.complexAlbaneseMap hg) ≫ D.ballAlbaneseProjector j =
      if i = j then D.componentComplexInclusion i ≫ D.pel.complexAlbaneseMap hg else 1 := by
  let F := Over.pullback D.pel.generic ⋙ Over.pullback D.pel.complexGenericPoint
  have H := congrArg F.map (BallFormsProjector.modelComponent_projector D.pel hg i j)
  simpa only [F, Data.ActiveHeckeThetaData.ballAlbaneseProjector, Data.ActiveHeckeThetaData.componentComplexInclusion,
    AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexAlbaneseMap, AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.albaneseMap,
    Functor.comp_map, Functor.map_comp, apply_ite, Functor.map_one, Category.assoc] using H

theorem Data.ActiveHeckeThetaData.ballFormsProjector_component (hg : D.pel.HasIntegralModelGeometry) (i j : Fin D.pel.componentCount)
    (ω : D.pel.OneFormsA) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i) (D.pel.albanesePullback hg (D.ballFormsProjector j ω)) =
      if i = j then AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i) (D.pel.albanesePullback hg ω) else 0 := by
  change (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i) ∘ₗ
    (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.pel.complexAlbaneseMap hg) ∘ₗ AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.ballAlbaneseProjector j))) ω = _
  rw [← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, ← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, ← Category.assoc, D.componentAlbanese_projector hg]
  split_ifs
  · rw [AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp]
    rfl
  · rw [CategoryTheory.Hom.one_def, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_constant]
    rfl

end

end OAI.RepresentationTheory.Theta.Geometric
