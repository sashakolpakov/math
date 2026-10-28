import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalChartPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin
import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalTransition
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable

/-! # Immersion Normal Recenter -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Normal cohomology classes under genuine recentering

Recentering translates only the tangential coordinate and shrinks the
verified normal neighborhood. Its normal coordinate is unchanged. Actual
relative cohomology pullback therefore identifies the recentered rational
class with restriction of the original class, and the two give the same
germ at the new center.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace Filter
open OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles
open scoped _root_.Topology _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section

variable {M N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

/-- The actual recentered neighborhood is contained in the original one. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterWithin_neighborhood_subset_original
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (P.recenterWithin z hz U hU).neighborhood ⊆ P.neighborhood :=
  (P.recenterWithin_neighborhood_subset z hz U hU).trans Set.inter_subset_left

/-- Inclusion from the genuine recentered neighborhood preserves the
actual normal-coordinate map. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCoordinate_comp_recenterWithin_inclusion
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N))
        (P.recenterWithin_neighborhood_subset_original z hz U hU) ≫
          P.normalCoordinate = (P.recenterWithin z hz U hU).normalCoordinate := by
  ext y
  change (P.ambientChart y.val).2 =
    ((P.recenterWithin z hz U hU).ambientChart y.val).2
  exact (P.recenterWithin_normalCoordinate z hz U hU y.val).symm

/-- Restriction between the actual relative cohomology groups of the
original and recentered normal neighborhoods. -/
abbrev ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterWithinCohomologyRestriction
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) (n : ℕ) :
    P.relativeCohomology (ModuleCat.of ℚ ℚ) n ⟶
      (P.recenterWithin z hz U hU).relativeCohomology (ModuleCat.of ℚ ℚ) n :=
  CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N)
    (P.recenterWithin_neighborhood_subset_original z hz U hU) (Set.range f) n

/-- This restriction is exactly the map of the existing relative
cohomology presheaf, with the complement of the same full image. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.recenterWithinCohomologyRestriction_eq_presheaf
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) (n : ℕ) :
    P.recenterWithinCohomologyRestriction z hz U hU n =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ n).map
        (homOfLE (show (P.recenterWithin z hz U hU).openNeighborhood ≤
          P.openNeighborhood from P.recenterWithin_neighborhood_subset_original z hz U hU)).op :=
  rfl

/-- The actual normal pullback commutes with restriction to the recentered
neighborhood in every cohomological degree. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) (n : ℕ) :
    P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫
        P.recenterWithinCohomologyRestriction z hz U hU n =
      (P.recenterWithin z hz U hU).normalCohomologyMap (ModuleCat.of ℚ ℚ) n := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) P.normalCoordinate
      P.normalCoordinate_mapsTo n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of N))
        (P.recenterWithin_neighborhood_subset_original z hz U hU))
      (fun _ hy => hy) n = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap
  congr 1

variable [NormedSpace ℝ E] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual recentered rational class is restriction of the original
class because both are pullbacks of the same normalized normal class. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    P.recenterWithinCohomologyRestriction z hz U hU (2 * Module.finrank ℂ F)
        P.rationalClass = (P.recenterWithin z hz U hU).rationalClass := by
  rw [P.rationalClass_eq_pullback, (P.recenterWithin z hz U hU).rationalClass_eq_pullback]
  exact ConcreteCategory.congr_hom
    (P.normalCohomologyMap_recenterWithin z hz U hU (2 * Module.finrank ℂ F))
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F)

/-- Recentering does not change the actual relative-cohomology germ at
the new center, even when the original pair was centered elsewhere. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_germ_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * Module.finrank ℂ F)).germ P.openNeighborhood (f z) hz P.rationalClass =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * Module.finrank ℂ F)).germ (P.recenterWithin z hz U hU).openNeighborhood
        (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood
          (P.recenterWithin z hz U hU).rationalClass := by
  have h := (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
    (2 * Module.finrank ℂ F)).germ_res_apply
      (homOfLE (show (P.recenterWithin z hz U hU).openNeighborhood ≤ P.openNeighborhood
        from P.recenterWithin_neighborhood_subset_original z hz U hU))
      (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood P.rationalClass
  exact h.symm.trans (congrArg
    (fun c : (P.recenterWithin z hz U hU).relativeCohomology (ModuleCat.of ℚ ℚ)
        (2 * Module.finrank ℂ F) =>
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
        (2 * Module.finrank ℂ F)).germ (P.recenterWithin z hz U hU).openNeighborhood
          (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood c)
    (P.rationalClass_recenterWithin z hz U hU))

end

variable {M N E : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : M → N} {x : M} {p : ℕ} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)

/-- In the explicit degree `2p`, the actual recentered normalized class
is still precisely the restriction of the original normalized class. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    P.recenterWithinCohomologyRestriction z hz U hU (2 * p)
      P.rationalClassFin = (P.recenterWithin z hz U hU).rationalClassFin := by
  rw [P.rationalClassFin_eq_normalPullback,
    (P.recenterWithin z hz U hU).rationalClassFin_eq_normalPullback]
  exact ConcreteCategory.congr_hom
    (P.normalCohomologyMap_recenterWithin z hz U hU (2 * p))
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

/-- The actual relative-cohomology germ in degree `2p` is unchanged by
recentering at any image point of the verified normal neighborhood. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_germ_recenterWithin
    (z : M) (hz : f z ∈ P.neighborhood) (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * p)).germ P.openNeighborhood (f z) hz P.rationalClassFin =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * p)).germ (P.recenterWithin z hz U hU).openNeighborhood
        (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood
          (P.recenterWithin z hz U hU).rationalClassFin := by
  have h := (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
    (2 * p)).germ_res_apply
      (homOfLE (show (P.recenterWithin z hz U hU).openNeighborhood ≤ P.openNeighborhood
        from P.recenterWithin_neighborhood_subset_original z hz U hU))
      (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood P.rationalClassFin
  exact h.symm.trans (congrArg
    (fun c : (P.recenterWithin z hz U hU).relativeCohomology (ModuleCat.of ℚ ℚ) (2 * p) =>
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
        (2 * p)).germ (P.recenterWithin z hz U hU).openNeighborhood
          (f z) (P.recenterWithin z hz U hU).point_mem_neighborhood c)
    (P.rationalClassFin_recenterWithin z hz U hU))

variable [NormedSpace ℂ E]

/-- At every image point in an actual overlap, two differentiable normal
pairs give the same relative-cohomology germ, even if their original
centers differ. Both are genuinely recentered and shrunk into the overlap
before applying the checked same-center transition theorem. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_germ_eq_on_overlap
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
    {y : M} (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f y)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (z : M) (hzP : f z ∈ P.neighborhood) (hzQ : f z ∈ Q.neighborhood) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * p)).germ P.openNeighborhood (f z) hzP P.rationalClassFin =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
      (2 * p)).germ Q.openNeighborhood (f z) hzQ Q.rationalClassFin := by
  let W := P.neighborhood ∩ Q.neighborhood
  have hW : W ∈ 𝓝 (f z) :=
    (P.isOpen_neighborhood.inter Q.isOpen_neighborhood).mem_nhds ⟨hzP, hzQ⟩
  let Pz := P.recenterWithin z hzP W hW
  let Qz := Q.recenterWithin z hzQ W hW
  have hPz : Pz.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)) :=
    P.recenterWithin_ambientChart_mdifferentiable hP z hzP W hW
  have hQz : Qz.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)) :=
    Q.recenterWithin_ambientChart_mdifferentiable hQ z hzQ W hW
  exact (P.rationalClassFin_germ_recenterWithin z hzP W hW).trans
    ((Pz.rationalClassFin_germ_eq_of_charts Qz hPz hQz).trans
      (Q.rationalClassFin_germ_recenterWithin z hzQ W hW).symm)

end

end OAI.AlgebraicGeometry
