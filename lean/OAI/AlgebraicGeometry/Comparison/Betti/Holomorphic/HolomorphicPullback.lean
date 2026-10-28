import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRhamComplex
import OAI.Analysis.DifferentialForms.Manifold.PurePullback
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback

/-! # Holomorphic Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback

noncomputable section

section

/-! Holomorphic pullback preserves the independently defined holomorphic de Rham complex. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]
  (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)

def pullback (n : ℕ) : DeRhamComplex.forms F N n →ₗ[ℂ] DeRhamComplex.forms E M n :=
  (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.pullback g hg |>.comp (DeRhamComplex.forms F N n).subtype).codRestrict _ (by
    intro a
    apply (DeRhamComplex.mem_forms_iff_derivative_pure n _).mpr
    change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M (n + 1) 0
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) (DeRhamComplex.inclusion F N n a))).val
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback]
    exact (DeRhamComplex.derivative_pure n a).pullback g hg)

theorem pullback_inclusion (n : ℕ) (a : DeRhamComplex.forms F N n) :
    DeRhamComplex.inclusion E M n (HolomorphicPullback.pullback g hg n a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) (DeRhamComplex.inclusion F N n a) := rfl

theorem pullback_differential (n : ℕ) (a : DeRhamComplex.forms F N n) :
    DeRhamComplex.differential E M n (HolomorphicPullback.pullback g hg n a) =
      HolomorphicPullback.pullback g hg (n + 1) (DeRhamComplex.differential F N n a) := by
  apply Subtype.ext
  apply Subtype.ext
  change DeRhamComplex.inclusion E M (n + 1) (DeRhamComplex.differential E M n (HolomorphicPullback.pullback g hg n a)) =
    DeRhamComplex.inclusion E M (n + 1) (HolomorphicPullback.pullback g hg (n + 1) (DeRhamComplex.differential F N n a))
  rw [DeRhamComplex.inclusion_differential, pullback_inclusion, pullback_inclusion,
    DeRhamComplex.inclusion_differential, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback]

def pullbackCochainMap : DeRhamComplex.complex F N ⟶ DeRhamComplex.complex E M :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (HolomorphicPullback.pullback g hg n)) (fun n => by
    rw [DeRhamComplex.complex_d, DeRhamComplex.complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact pullback_differential g hg n a)

theorem pullbackCochainMap_inclusion :
    pullbackCochainMap g hg ≫ DeRhamComplex.inclusionCochainMap E M =
      DeRhamComplex.inclusionCochainMap F N ≫ Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

end

/-! Identity and composition laws for actual holomorphic-form pullback. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E F G M N P : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℂ, G) ∞ P]

theorem inclusion_injective (n : ℕ) : Function.Injective (DeRhamComplex.inclusion E M n) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem pullback_id (n : ℕ) (a : DeRhamComplex.forms E M n) :
    HolomorphicPullback.pullback (id : M → M) contMDiff_id n a = a := by
  apply Subtype.ext
  exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.pullback_id a.val

theorem pullback_comp (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (h : N → P) (hh : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, G) ∞ h) (n : ℕ) (a : DeRhamComplex.forms G P n) :
    HolomorphicPullback.pullback (h ∘ g) (hh.comp hg) n a = HolomorphicPullback.pullback g hg n (HolomorphicPullback.pullback h hh n a) := by
  apply Subtype.ext
  exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.pullback_comp g hg h hh a.val

theorem pullbackCochainMap_id :
    pullbackCochainMap (id : M → M) contMDiff_id = 𝟙 (DeRhamComplex.complex E M) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact pullback_id n a

theorem pullbackCochainMap_comp (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (h : N → P) (hh : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, G) ∞ h) :
    pullbackCochainMap (h ∘ g) (hh.comp hg) = pullbackCochainMap h hh ≫ pullbackCochainMap g hg := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact pullback_comp g hg h hh n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback
