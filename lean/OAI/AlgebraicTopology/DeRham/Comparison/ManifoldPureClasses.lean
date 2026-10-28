import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham
import OAI.Analysis.DifferentialForms.Manifold.BidegreeInvariant
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Manifold Pure Classes -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses

noncomputable section

/-!
# Global classes represented by closed pure forms

The underlying real smooth structure is derived from the genuine holomorphic
atlas. We then use the actual global exterior derivative and de Rham quotient,
and the chart-invariant pure bidegree condition on tangent covector fields.
These are global analytic classes; no comparison to Betti cohomology or
algebraic cycle classes is assumed.
-/

open scoped _root_.Manifold ContDiff

universe u v
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  (M : Type v) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

local instance realSmoothManifold : IsManifold 𝓘(ℝ, E) ∞ M :=
  Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

/-- Genuine global smooth forms that are closed and of pure bidegree. -/
def closedPureManifoldForms (p q : ℕ) : Submodule ℂ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q)) :=
  Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q) ⊓ Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M p q

@[simp]
theorem mem_closedPureManifoldForms (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q)) :
    form ∈ closedPureManifoldForms E M p q ↔
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 ∧
        Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)) := Iff.rfl

/-- Pure global forms inside the actual kernel of the global exterior derivative. -/
def pureClosedManifoldForms (p q : ℕ) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q)) :=
  (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M p q).comap (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q)).subtype

@[simp]
theorem mem_pureClosedManifoldForms (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q)) :
    form ∈ pureClosedManifoldForms E M p q ↔
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q (form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)) := Iff.rfl

/-- Both concrete descriptions of the closed pure form space agree. -/
theorem pureClosedManifoldForms_map_subtype (p q : ℕ) :
    (pureClosedManifoldForms E M p q).map (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q)).subtype =
      closedPureManifoldForms E M p q :=
  Submodule.map_comap_subtype (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q))
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M p q)

/-- Restrict the actual global de Rham class map to closed pure forms. -/
def manifoldPureFormClass (p q : ℕ) :
    pureClosedManifoldForms E M p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q) :=
  (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M (p + q)).comp (pureClosedManifoldForms E M p q).subtype

/-- The global de Rham subspace represented by closed pure forms. -/
def manifoldPureDeRhamImage (p q : ℕ) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q)) :=
  (pureClosedManifoldForms E M p q).map (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M (p + q))

/-- The global image is the range of the restricted global class map. -/
theorem range_manifoldPureFormClass (p q : ℕ) :
    LinearMap.range (manifoldPureFormClass E M p q) = manifoldPureDeRhamImage E M p q := by
  rw [manifoldPureFormClass, LinearMap.range_comp, Submodule.range_subtype]
  rfl

/-- Image membership is exactly existence of a genuine closed pure representative. -/
theorem mem_manifoldPureDeRhamImage_iff (p q : ℕ)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q)) :
    α ∈ manifoldPureDeRhamImage E M p q ↔
      ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q),
        Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q (form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)) ∧
          Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M (p + q) form = α := by
  simp only [manifoldPureDeRhamImage, Submodule.mem_map, mem_pureClosedManifoldForms]

/-- The same criterion using the ordinary global equation `d form = 0`. -/
theorem mem_manifoldPureDeRhamImage_iff_smooth (p q : ℕ)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q)) :
    α ∈ manifoldPureDeRhamImage E M p q ↔
      ∃ (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q)) (hform : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0),
        Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)) ∧
          Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M (p + q) ⟨form, hform⟩ = α := by
  rw [mem_manifoldPureDeRhamImage_iff]
  constructor
  · rintro ⟨⟨form, hform⟩, hpure, hclass⟩
    exact ⟨form, hform, hpure, hclass⟩
  · rintro ⟨form, hform, hpure, hclass⟩
    exact ⟨⟨form, hform⟩, hpure, hclass⟩

/-- Holomorphic chart invariance allows purity to be checked in one atlas chart
at each point, with no extra condition on the selected atlas. -/
theorem mem_manifoldPureDeRhamImage_iff_chartAt (p q : ℕ)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q)) :
    α ∈ manifoldPureDeRhamImage E M p q ↔
      ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q),
        (∀ x : M, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q
          ((form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart (chartAt E x) (chartAt E x x))) ∧
          Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M (p + q) form = α := by
  simp only [mem_manifoldPureDeRhamImage_iff, Analysis.DifferentialForms.Manifold.BidegreeInvariant.hasManifoldBidegree_iff_chartAt]

/-- The corresponding global pure image in the literal closed/exact quotient. -/
def manifoldPureQuotientImage (p q : ℕ) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient E M (p + q)) :=
  (pureClosedManifoldForms E M p q).map (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q)).mkQ

/-- The verified global de Rham quotient isomorphism preserves these actual images. -/
theorem manifoldPureDeRhamImage_eq_quotientImage (p q : ℕ) :
    manifoldPureDeRhamImage E M p q = (manifoldPureQuotientImage E M p q).map
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso E M (p + q)).toLinearEquiv.symm.toLinearMap :=
  Submodule.map_comp (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q)).mkQ
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso E M (p + q)).toLinearEquiv.symm.toLinearMap
    (pureClosedManifoldForms E M p q)

/-- A global closed pure form has zero class precisely when it is globally exact. -/
theorem manifoldPureFormClass_eq_zero_iff (p q : ℕ) (form : pureClosedManifoldForms E M p q) :
    manifoldPureFormClass E M p q form = 0 ↔
      ∃ η : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q - 1),
        Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative E M (p + q) η = form.val.val :=
  Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff E M (p + q) form.val

/-- The global quotient criterion is membership in pure closed forms plus exact forms. -/
theorem manifoldQuotientClass_mem_pureImage_iff (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q)) :
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q)).mkQ form ∈ manifoldPureQuotientImage E M p q ↔
      form ∈ pureClosedManifoldForms E M p q ⊔ Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q) := by
  change form ∈ ((pureClosedManifoldForms E M p q).map
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q)).mkQ).comap
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E M (p + q)).mkQ ↔ _
  rw [Submodule.comap_map_mkQ, sup_comm]

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses
