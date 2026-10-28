import OAI.RepresentationTheory.Theta.Geometric.OneFormBettiFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.BallFormsProjector

/-! # Projector -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Commutation of actual rational form pullbacks with an algebraic
projector implies commutation on the full original rational Betti H1. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)

local instance Data.ActiveHeckeThetaData.rationalProjectorGroup : GrpObj D.pel.albaneseGroup.X := D.pel.albaneseGroup.grp
local instance Data.ActiveHeckeThetaData.rationalProjectorComm : IsCommMonObj D.pel.albaneseGroup.X := D.pel.albaneseGroup.comm

include hg in
theorem Data.ActiveHeckeThetaData.rationalH1_projector_of_forms (a : D.pel.EndQ)
    (F : Module.End ℂ D.pel.OneFormsA) (H : Module.End ℚ D.pel.H1)
    (hF : D.IsRationalFormsPullback a F) (hH : D.pel.IsRationalH1Pullback a H)
    (j : Fin D.pel.componentCount)
    (hc : F.comp (D.ballFormsProjector j) = (D.ballFormsProjector j).comp F) :
    H.comp (D.ballH1Projector j) = (D.ballH1Projector j).comp H := by
  obtain ⟨n, hn, b, hb⟩ := hF.1
  have hf := hF.2 n hn b hb
  have hh := hH.2 n hn b hb
  let f := (Over.pullback D.pel.complexGenericPoint).map (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap D.pel.albaneseGroup.X b)
  let p := D.ballAlbaneseProjector j
  have hfp : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (f ≫ p) = AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (p ≫ f) := by
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp]
    change (D.pel.pullbackForms b).comp (D.ballFormsProjector j) =
      (D.ballFormsProjector j).comp (D.pel.pullbackForms b)
    rw [← hf, LinearMap.smul_comp, LinearMap.comp_smul, hc]
  have hbetti := OneFormBettiFaithfulness.abelian_rationalBetti_eq_of_forms
    (D.pel.actualComplexAlbaneseVariety hg).variety (D.pel.actualComplexAlbaneseVariety hg)
    (f ≫ p) (p ≫ f) hfp
  change AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ (f ≫ p) 1 = AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ (p ≫ f) 1 at hbetti
  rw [AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ_comp, AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ_comp] at hbetti
  change (D.pel.pullbackH1Integral b).comp (D.ballH1Projector j) =
    (D.ballH1Projector j).comp (D.pel.pullbackH1Integral b) at hbetti
  rw [← hh, LinearMap.smul_comp, LinearMap.comp_smul] at hbetti
  exact (smul_right_injective (M := Module.End ℚ D.pel.H1)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))) hbetti

end

end OAI.RepresentationTheory.Theta.Geometric
