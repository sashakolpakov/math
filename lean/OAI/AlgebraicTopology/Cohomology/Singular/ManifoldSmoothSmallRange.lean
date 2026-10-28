import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision

/-! # Manifold Smooth Small Range -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallRange

noncomputable section

/-!
# The actual image of cover-small smooth chains

The image of the inclusion of small smooth chains consists exactly of the
smooth chains whose ordinary singular support is cover-small. The proof uses
the canonical finite-support coefficients of the actual simplicial chain
complexes, so it applies directly to ordinary subdivision estimates.
-/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An injective map on simplices induces an injective map on actual integral
chains in the same degree. -/
theorem simplicialIntegralChainMap_injective {S T : SSet.{0}} (f : S ⟶ T)
    (n : ℕ) (hf : Function.Injective (f.app (.op ⦋n⦌))) :
    Function.Injective ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n) := by
  intro a b hab
  apply (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients S n).injective
  apply Finsupp.mapDomain_injective hf
  rw [← AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients_map, ← AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients_map, hab]

/-- The image of a degreewise injective simplicial chain map is determined
by its actual simplex support. -/
theorem mem_range_simplicialIntegralChainMap_iff {S T : SSet.{0}} (f : S ⟶ T)
    (n : ℕ) (hf : Function.Injective (f.app (.op ⦋n⦌)))
    (c : (T.chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    c ∈ LinearMap.range ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n).hom ↔
      ∀ t ∈ (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients T n c).support,
        t ∈ Set.range (f.app (.op ⦋n⦌)) := by
  constructor
  · rintro ⟨b, rfl⟩ t ht
    rw [AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients_map] at ht
    exact Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp ht)
  · intro hc
    have hcoeff : AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients T n c ∈
        Set.range (Finsupp.mapDomain (f.app (.op ⦋n⦌))) := by
      apply (Finsupp.mem_range_mapDomain_iff _ hf _).2
      intro t ht
      by_contra hne
      exact ht (hc t (Finsupp.mem_support_iff.mpr hne))
    obtain ⟨b, hb⟩ := hcoeff
    refine ⟨(AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients S n).symm b, ?_⟩
    apply (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients T n).injective
    rw [AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients_map]
    exact (congrArg (Finsupp.mapDomain (f.app (.op ⦋n⦌)))
      ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients S n).apply_symm_apply b)).trans hb

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Set X)

/-- The small smooth inclusion is injective on its genuine simplices. -/
theorem manifoldSmoothSmallInclusion_app_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((ManifoldSmoothSmall.manifoldSmoothSmallInclusion E X U).app n) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun σ : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).obj n => σ.val) hab

/-- Within the smooth simplex type, the small smooth image is precisely the
ordinary cover-smallness condition. -/
theorem mem_range_manifoldSmoothSmallInclusion_iff (n : SimplexCategoryᵒᵖ)
    (σ : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).obj n) :
    σ ∈ Set.range ((ManifoldSmoothSmall.manifoldSmoothSmallInclusion E X U).app n) ↔
      σ.val ∈ (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex (TopCat.of X) U).obj n := by
  constructor
  · rintro ⟨τ, rfl⟩
    exact τ.property.1
  · intro hσ
    exact ⟨⟨σ.val, hσ, σ.property⟩, rfl⟩

/-- The inclusion of actual small smooth integral chains is degreewise
injective, independently of any cover or subdivision hypothesis. -/
theorem manifoldSmoothSmallIntegralChainInclusion_injective (n : ℕ) :
    Function.Injective ((ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E X U).f n) :=
  simplicialIntegralChainMap_injective (ManifoldSmoothSmall.manifoldSmoothSmallInclusion E X U) n
    (manifoldSmoothSmallInclusion_app_injective E X U _)

/-- The range criterion first expressed in coefficients indexed by the
smooth simplices themselves. -/
theorem mem_range_manifoldSmoothSmallIntegralChainInclusion_smoothSupport_iff
    (n : ℕ) (c : (ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E X).X n) :
    c ∈ LinearMap.range ((ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E X U).f n).hom ↔
      ∀ σ ∈ (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients
        (ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).toSSet n c).support,
        σ.val ∈ (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex (TopCat.of X) U).obj (.op ⦋n⦌) := by
  rw [mem_range_simplicialIntegralChainMap_iff (ManifoldSmoothSmall.manifoldSmoothSmallInclusion E X U) n
    (manifoldSmoothSmallInclusion_app_injective E X U _)]
  constructor
  · intro h σ hσ
    exact (mem_range_manifoldSmoothSmallInclusion_iff E X U _ σ).mp (h σ hσ)
  · intro h σ hσ
    exact (mem_range_manifoldSmoothSmallInclusion_iff E X U _ σ).mpr (h σ hσ)

/-- The ambient ordinary coefficients of a smooth chain are extension along
the actual inclusion of smooth simplices. -/
theorem manifoldSmoothIntegralChainInclusion_coefficients (n : ℕ)
    (c : (ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E X).X n) :
    AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles.singularChainCoefficients (TopCat.of X) n
        ((ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E X).f n c) =
      Finsupp.mapDomain Subtype.val (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients
        (ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).toSSet n c) :=
  AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients_map (ManifoldSmooth.manifoldSmoothInclusion E X) n c

/-- A smooth chain lies in the actual small smooth image exactly when its
ambient ordinary singular support is cover-small. -/
theorem mem_range_manifoldSmoothSmallIntegralChainInclusion_iff
    (n : ℕ) (c : (ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E X).X n) :
    c ∈ LinearMap.range ((ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E X U).f n).hom ↔
      ∀ σ ∈ AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles.singularChainSupport ((ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E X).f n c),
        σ ∈ (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex (TopCat.of X) U).obj (.op ⦋n⦌) := by
  rw [mem_range_manifoldSmoothSmallIntegralChainInclusion_smoothSupport_iff]
  constructor
  · intro hc σ hσ
    change σ ∈ (AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles.singularChainCoefficients (TopCat.of X) n
      ((ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E X).f n c)).support at hσ
    rw [manifoldSmoothIntegralChainInclusion_coefficients] at hσ
    obtain ⟨τ, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero
      (Finsupp.mem_support_iff.mp hσ)
    apply hc τ
    apply Finsupp.mem_support_iff.mpr
    simpa only [Finsupp.mapDomain_apply_of_injective Subtype.val_injective] using!
      (Finsupp.mem_support_iff.mp hσ)
  · intro hc σ hσ
    apply hc σ.val
    change σ.val ∈ (AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles.singularChainCoefficients (TopCat.of X) n
      ((ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E X).f n c)).support
    rw [manifoldSmoothIntegralChainInclusion_coefficients]
    apply Finsupp.mem_support_iff.mpr
    simpa only [Finsupp.mapDomain_apply_of_injective Subtype.val_injective] using!
      (Finsupp.mem_support_iff.mp hσ)

/-- Equivalently, the small smooth image is the inverse image of the
ordinary small-chain image under the actual smooth inclusion. -/
theorem mem_range_manifoldSmoothSmallIntegralChainInclusion_iff_ambient_range
    (n : ℕ) (c : (ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E X).X n) :
    c ∈ LinearMap.range ((ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E X U).f n).hom ↔
      (ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E X).f n c ∈
        LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion (TopCat.of X) U).f n).hom := by
  rw [mem_range_manifoldSmoothSmallIntegralChainInclusion_iff,
    AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.mem_range_smallIntegralChainInclusion_iff]

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallRange
