import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Analytic Invariant Covectors -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticInvariantCovectors

noncomputable section

section

/-! # Analytic coefficients of invariant complex cotangent fields

The coefficients come from the derivative of the actual analytic group
operations. This avoids assuming a general differentiable-to-analytic theorem.
-/

open scoped _root_.Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℂ, E) ω G]

/-- Actual left-translation cotangent coefficients are analytic in every original chart. -/
theorem analyticInvariantCovectorCoefficient (α : E →L[ℂ] ℂ)
    (c d : OpenPartialHomeomorph G E) (hc : c ∈ atlas E G) (hd : d ∈ atlas E G)
    (h1 : (1 : G) ∈ d.source) {y : E} (hy : y ∈ c.target) :
    ContDiffAt ℂ ω
      (fun z => α.comp (fderiv ℂ (fun w => d ((c.symm z)⁻¹ * c.symm w)) z)) y := by
  have hcinv : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω c.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
  have hc₁ : ContMDiffAt 𝓘(ℂ, E × E) 𝓘(ℂ, E) ω
      (fun z : E × E => c.symm z.1) (y, y) :=
    hcinv.comp (y, y) contDiffAt_fst.contMDiffAt
  have hc₂ : ContMDiffAt 𝓘(ℂ, E × E) 𝓘(ℂ, E) ω
      (fun z : E × E => c.symm z.2) (y, y) :=
    hcinv.comp (y, y) contDiffAt_snd.contMDiffAt
  have hm : ContMDiffAt 𝓘(ℂ, E × E) 𝓘(ℂ, E) ω
      (fun z : E × E => (c.symm z.1)⁻¹ * c.symm z.2) (y, y) := hc₁.inv.mul hc₂
  have hd' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω d
      ((c.symm y)⁻¹ * c.symm y) := by
    rw [inv_mul_cancel]
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) h1
  have ht : ContDiffAt ℂ ω
      (fun z : E × E => d ((c.symm z.1)⁻¹ * c.symm z.2)) (y, y) :=
    (hd'.comp (y, y) hm).contDiffAt
  exact contDiffAt_const.clm_comp (ht.fderiv contDiffAt_id (by simp))

end

/-! # Analytic invariant cotangent coefficients along an actual analytic map

The source and target may use different model spaces. This is the coordinate
formula for pullback of the invariant cotangent field by the given actual map.
-/

open scoped _root_.Manifold ContDiff

variable {E F M G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [Group G] [TopologicalSpace G] [ChartedSpace F G] [LieGroup 𝓘(ℂ, F) ω G]

/-- The actual invariant-covector pullback coefficients are analytic in source coordinates. -/
theorem analyticInvariantCovectorCoefficientAlong
    (f : M → G) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f) (α : F →L[ℂ] ℂ)
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph G F)
    (hc : c ∈ atlas E M) (hd : d ∈ atlas F G)
    (h1 : (1 : G) ∈ d.source) {y : E} (hy : y ∈ c.target) :
    ContDiffAt ℂ ω
      (fun z => α.comp (fderiv ℂ
        (fun w => d ((f (c.symm z))⁻¹ * f (c.symm w))) z)) y := by
  have hcinv : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω c.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
  have hfc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) ω (f ∘ c.symm) y :=
    (hf.contMDiffAt).comp y hcinv
  have hc₁ : ContMDiffAt 𝓘(ℂ, E × E) 𝓘(ℂ, F) ω
      (fun z : E × E => f (c.symm z.1)) (y, y) :=
    hfc.comp (f := Prod.fst) (g := f ∘ c.symm) (y, y) contDiffAt_fst.contMDiffAt
  have hc₂ : ContMDiffAt 𝓘(ℂ, E × E) 𝓘(ℂ, F) ω
      (fun z : E × E => f (c.symm z.2)) (y, y) :=
    hfc.comp (f := Prod.snd) (g := f ∘ c.symm) (y, y) contDiffAt_snd.contMDiffAt
  have hm : ContMDiffAt 𝓘(ℂ, E × E) 𝓘(ℂ, F) ω
      (fun z : E × E => (f (c.symm z.1))⁻¹ * f (c.symm z.2)) (y, y) := hc₁.inv.mul hc₂
  have hd' : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, F) ω d
      ((f (c.symm y))⁻¹ * f (c.symm y)) := by
    rw [inv_mul_cancel]
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) h1
  have ht : ContDiffAt ℂ ω
      (fun z : E × E => d ((f (c.symm z.1))⁻¹ * f (c.symm z.2))) (y, y) :=
    (hd'.comp (y, y) hm).contDiffAt
  exact contDiffAt_const.clm_comp (ht.fderiv contDiffAt_id (by simp))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticInvariantCovectors
