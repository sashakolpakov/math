import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Presheaf
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham
import OAI.Analysis.DifferentialForms.Manifold.CechDeRham

/-! # Presheaf Inclusion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.PresheafInclusion

noncomputable section

/-! The holomorphic presheaf includes into the actual smooth form presheaf, with its genuine restrictions. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def openInclusionCochainMap (U : Opens M) : DeRhamComplex.complex E U ⟶ Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex E U :=
  DeRhamComplex.inclusionCochainMap E U ≫ (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E U).inv

theorem openInclusionCochainMap_restrict {U V : Opens M} (h : U ≤ V) :
    Presheaf.restrict E M h ≫ openInclusionCochainMap E M U =
      openInclusionCochainMap E M V ≫ Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict E h := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).injective
  change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm
        (DeRhamComplex.inclusion E U n (HolomorphicPullback.pullback (Opens.inclusion h)
          (contMDiff_inclusion (I := 𝓘(ℂ, E)) (n := ∞) h) n a))) =
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V n).symm (DeRhamComplex.inclusion E V n a)))
  rw [LinearEquiv.apply_symm_apply, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict, LinearEquiv.apply_symm_apply]
  rfl

def inclusionPresheafMap : Presheaf.presheafOfComplexes E M ⟶ Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamPresheaf E M where
  app U := openInclusionCochainMap E M U.unop
  naturality _ _ f := openInclusionCochainMap_restrict E M (leOfHom f.unop)

def inclusionPresheafCochainMap : Presheaf.presheafComplex E M ⟶ Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M where
  f n :=
    { app := fun U => (openInclusionCochainMap E M U.unop).f n
      naturality := fun U V f => congrArg (fun k => k.f n)
        ((inclusionPresheafMap E M).naturality f) }
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    apply NatTrans.ext
    funext U
    have h := (openInclusionCochainMap E M U.unop).comm i (i + 1)
    rw [Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex_d] at h
    rw [Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d]
    exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.PresheafInclusion
