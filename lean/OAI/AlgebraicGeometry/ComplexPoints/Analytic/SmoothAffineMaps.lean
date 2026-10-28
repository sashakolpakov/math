import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Smooth Affine Maps -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineMaps

noncomputable section

/-!
# Smooth maps of actual smooth affine complex point manifolds

The manifold structures here are the established regular-coordinate atlases
of smooth integral complex algebras. Pullback by an algebra homomorphism and
evaluation of an actual regular function are analytic in those atlases.
-/

open scoped ContDiff _root_.Manifold
open ChartedSpace

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.Smooth ℂ A]
variable [CommRing B] [Algebra ℂ B] [IsDomain B] [Algebra.Smooth ℂ B]

local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
local notation "ModelB" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ)

/-- The actual pullback map is analytic in any two preferred regular charts. -/
theorem contDiffOn_smoothDomain_comap_charts (h : A →ₐ[ℂ] B)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ContDiffOn ℂ ω
      (fun z => chartAt ModelA y (((chartAt ModelB x).symm z).comp h))
      ((chartAt ModelB x).target ∩
        {z | ((chartAt ModelB x).symm z).comp h ∈ (chartAt ModelA y).source}) := by
  have he : chartAt ModelB x ∈
      SmoothSchemeManifold.affineRegularAtlas B (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) := chart_mem_atlas ModelB x
  have hf : chartAt ModelA y ∈
      SmoothSchemeManifold.affineRegularAtlas A (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) := chart_mem_atlas ModelA y
  obtain ⟨g, hg, hcoords⟩ := hf.2
  exact SmoothSchemeManifold.contDiffOn_affineChartComapTransition h _ _ he.1 g hg hcoords

/-- Pullback by an actual complex algebra homomorphism is analytic, hence of
every differentiability order, on the established smooth affine manifolds. -/
theorem contMDiff_smoothDomain_comap (h : A →ₐ[ℂ] B) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, ModelB)) (𝓘(ℂ, ModelA)) r (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) := by
  apply contMDiff_iff.mpr
  refine ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h).continuous, ?_⟩
  intro x y
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap, ContinuousMap.coe_mk,
    id_eq, Set.preimage, Set.mem_ofPred_eq, Set.ofPred_mem_eq]
    using (contDiffOn_smoothDomain_comap_charts h x y).of_le (show r ≤ ω from le_top)

/-- The same algebraic pullback is smooth for the scalar-restricted real
manifolds used by real differential forms with complex coefficients. -/
theorem real_contMDiff_smoothDomain_comap (h : A →ₐ[ℂ] B) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, ModelB)) (𝓘(ℝ, ModelA)) r (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) := by
  apply contMDiff_iff.mpr
  refine ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h).continuous, ?_⟩
  intro x y
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap, ContinuousMap.coe_mk,
    id_eq, Set.preimage, Set.mem_ofPred_eq, Set.ofPred_mem_eq]
    using ((contDiffOn_smoothDomain_comap_charts h x y).of_le
      (show r ≤ ω from le_top)).restrict_scalars ℝ

/-- Every actual regular function on a smooth integral affine complex scheme
is analytic in the established point-manifold structure. -/
theorem contMDiff_smoothDomain_eval (a : A) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, ModelA)) (𝓘(ℂ, ℂ)) r (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval a) := by
  apply contMDiff_iff.mpr
  refine ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a, ?_⟩
  intro x y
  have he : chartAt ModelA x ∈
      SmoothSchemeManifold.affineRegularAtlas A (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) := chart_mem_atlas ModelA x
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_source,
    Set.preimage_univ, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq, Set.mem_univ, Set.ofPred_true]
    using (he.1 a).of_le (show r ≤ ω from le_top)

/-- Regular-function evaluation is smooth on the underlying real manifold. -/
theorem real_contMDiff_smoothDomain_eval (a : A) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, ModelA)) (𝓘(ℝ, ℂ)) r (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval a) := by
  apply contMDiff_iff.mpr
  refine ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a, ?_⟩
  intro x y
  have he : chartAt ModelA x ∈
      SmoothSchemeManifold.affineRegularAtlas A (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) := chart_mem_atlas ModelA x
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_source,
    Set.preimage_univ, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq, Set.mem_univ, Set.ofPred_true]
    using ((he.1 a).of_le (show r ≤ ω from le_top)).restrict_scalars ℝ

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineMaps
