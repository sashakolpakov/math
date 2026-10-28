import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DeRhamSecondQuotient
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultSheafOneExact
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TwoStepLocalVanishing
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # Hodge Boundary Vanishing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.HodgeBoundaryVanishing

noncomputable section

/-! The actual de Rham double connecting class of a closed mixed form has zero holomorphic image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem manifoldDeRhamConnectingClass_holomorphic_zero
    (s : (DeRhamSecondQuotient.manifoldDeRhamSecondQuotient E M).obj.obj (op (⊤ : Opens M)))
    (hs : Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1
      ((DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M).hom.app (op (⊤ : Opens M)) s)) :
    CategoryTheory.Sheaf.H.map (DolbeaultComparison.locallyConstantComplexHolomorphicSheafMap (E := E) (M := M)) 2
      (DeRhamSecondQuotient.manifoldDeRhamConnectingClass E M s) = 0 := by
  let S := Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence E M
  let T := ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldDolbeaultZeroSequence (E := E) (M := M)
  have : Mono S.f := Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion_mono E M
  have : Mono T.f := ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf_mono
  apply Chern.Sheaf.TwoStepLocalVanishing.sheafTwoStepBoundary_vanishes_of_local_lifts
    (S := S) (T := T) (Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence_exact E M)
    ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldDolbeaultZeroSequence_exact
    DolbeaultComparison.manifoldDeRhamDolbeaultZeroComparison (PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)
    (PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap_squared E M 0) (DolbeaultSheafOneExact.pureManifoldDolbeaultOneSequence_exact E M) s
  intro U a ha
  change DolbeaultCharts.pureOpenManifoldDolbeaultD U 1 (OneFormProjection.openManifoldOneAntiProjection a) = 0
  apply Subtype.ext
  apply MixedDerivativeProjection.openManifoldOnePart_dbar_zero_of_mixed_derivative a
  have hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict le_top
      ((DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M).hom.app (op (⊤ : Opens M)) s) := by
    have hc := ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op U))
        (TwoStepQuotient.secondQuotientDifferential_comp S (Abelian.ManifoldDeRham.abelianManifoldFormSheafD E M 1)
          (Abelian.ManifoldDeRham.abelianManifoldFormSheafD_squared E M 0))) a
    change (DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M).hom.app (op U)
      ((cokernel.π (TwoStepQuotient.firstQuotientDifferential S)).hom.app (op U) a) = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a at hc
    calc
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = (DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M).hom.app (op U)
          ((cokernel.π (TwoStepQuotient.firstQuotientDifferential S)).hom.app (op U) a) := hc.symm
      _ = (DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M).hom.app (op U)
          (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict _ le_top s) := congrArg _ ha
      _ = _ := Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict (DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M) le_top s
  rw [hd]
  exact Open.ManifoldBidegree.openManifoldHasBidegree_restrict le_top hs

theorem exists_manifoldHodgeConnectingLift
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 2) (hform : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M 1 1 form.val.val) :
    ∃ s : (DeRhamSecondQuotient.manifoldDeRhamSecondQuotient E M).obj.obj (op (⊤ : Opens M)),
      (DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M).hom.app (op (⊤ : Opens M)) s =
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form.val ∧
      CategoryTheory.Sheaf.H.map (DolbeaultComparison.locallyConstantComplexHolomorphicSheafMap (E := E) (M := M)) 2
        (DeRhamSecondQuotient.manifoldDeRhamConnectingClass E M s) = 0 := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  have hclosed : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (⊤ : Opens M) form.val) = 0 := by
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, form.property, map_zero]
  obtain ⟨s, hs⟩ := DeRhamSecondQuotient.manifoldDeRhamSecondQuotient_exists_lift E M (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form.val) hclosed
  refine ⟨s, hs, manifoldDeRhamConnectingClass_holomorphic_zero s ?_⟩
  rw [hs]
  exact Open.ManifoldBidegree.openManifoldHasBidegree_onOpen ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (E := E) (M := M) (p := 1) (q := 1) form.val.val).mpr hform) ⊤

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.HodgeBoundaryVanishing
