import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity
import OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity

/-! # Normal Chart Purity -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Local purity at the actual relative-cohomology stalk

A fixed genuine normal neighborhood computes the stalk of relative
cohomology. Its smaller concentric normal neighborhoods form a cofinal
system, and all the actual restriction maps in that system are invertible.
This proves the stalk comparison without assuming that arbitrary
intersections of normal neighborhoods have product shape.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {M N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

/-- The genuine normal neighborhood as an object of the open-set category. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.openNeighborhood : Opens (TopCat.of N) :=
  ⟨P.neighborhood, P.isOpen_neighborhood⟩

/-- Actual restriction between normal neighborhoods agrees with the map
of the genuine relative-cohomology presheaf. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyPresheaf_restrict (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ n).map
        (homOfLE (show Q.openNeighborhood ≤ P.openNeighborhood from hQP)).op =
      CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n := rfl

/-- The genuine germ map from the cohomology of one normal neighborhood. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGerm (n : ℕ) :
    P.relativeCohomology (ModuleCat.of ℚ ℚ) n ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ n).stalk (f x) :=
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ n).germ
    P.openNeighborhood (f x) P.point_mem_neighborhood

/-- Actual germs commute with the actual restriction of normal neighborhoods. -/
@[reassoc]
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGerm_restrict (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (n : ℕ) :
    CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n ≫
        Q.relativeCohomologyGerm n = P.relativeCohomologyGerm n :=
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ n).germ_res
    (homOfLE (show Q.openNeighborhood ≤ P.openNeighborhood from hQP))
    (f x) Q.point_mem_neighborhood

variable [NormedSpace ℝ E]

/-- Restricting to a smaller neighborhood in the same actual normal chart
is an isomorphism in every degree. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalNeighborhoodRestriction_isIso (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart)
    (n : ℕ) :
    IsIso (CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n) := by
  have := P.normalCohomologyMap_isIso n
  have := Q.normalCohomologyMap_isIso n
  have : IsIso (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫
      CycleClass.Geometric.RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) n) := by
    rw [P.normalCohomologyMap_restrict Q hQP hchart n]
    infer_instance
  exact IsIso.of_isIso_comp_left (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n) _

/-- A normal neighborhood computes the actual relative-cohomology stalk.
The proof uses cofinal smaller neighborhoods and actual germ representatives. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGerm_isIso (n : ℕ) : IsIso (P.relativeCohomologyGerm n) := by
  apply AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso.germ_isIso_of_cofinal_restrictions
  intro U hxU
  obtain ⟨r, hr, hle, hsub⟩ := P.exists_restrictRadius_subset (U : Set N)
    (U.isOpen.mem_nhds hxU)
  let Q := P.restrictRadius r hr hle
  have hQP : Q.neighborhood ⊆ P.neighborhood := P.restrictRadius_neighborhood_subset r hr hle
  refine ⟨Q.openNeighborhood, Q.point_mem_neighborhood, hQP, hsub, ?_⟩
  rw [P.relativeCohomologyPresheaf_restrict Q hQP n]
  exact P.normalNeighborhoodRestriction_isIso Q hQP rfl n

/-- The isomorphism is the actual germ map, not a chosen identification. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGermIso (n : ℕ) :
    P.relativeCohomology (ModuleCat.of ℚ ℚ) n ≅
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ n).stalk (f x) := by
  have := P.relativeCohomologyGerm_isIso n
  exact asIso (P.relativeCohomologyGerm n)

@[simp]
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGermIso_hom (n : ℕ) :
    (P.relativeCohomologyGermIso n).hom = P.relativeCohomologyGerm n := rfl

/-- The actual normal coordinate followed by the actual germ gives the
normal-model comparison with the relative-cohomology stalk. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ≅
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ n).stalk (f x) :=
  P.relativeCohomologyIso n ≪≫ P.relativeCohomologyGermIso n

@[simp]
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso_hom (n : ℕ) :
    (P.normalStalkCohomologyIso n).hom =
      P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫ P.relativeCohomologyGerm n := by
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso, Iso.trans_hom, ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyIso_hom,
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyGermIso_hom]

/-- Shrinking the normal neighborhood while retaining the chart gives
exactly the same map into the stalk. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso_hom_eq (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart)
    (n : ℕ) :
    (P.normalStalkCohomologyIso n).hom = (Q.normalStalkCohomologyIso n).hom := by
  rw [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso_hom, ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalStalkCohomologyIso_hom,
    ← P.relativeCohomologyGerm_restrict Q hQP n, ← Category.assoc,
    P.normalCohomologyMap_restrict Q hQP hchart n]

variable [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The stalk in the top normal degree is the actual one-dimensional
rational module, with normalization from the complex normal coordinates. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalStalkTopCohomologyIso :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (2 * Module.finrank ℂ F)).stalk (f x) ≅ ModuleCat.of ℚ ℚ :=
  (P.normalStalkCohomologyIso (2 * Module.finrank ℂ F)).symm ≪≫
    CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso F

include P in
/-- Genuine relative-cohomology stalks vanish outside the top normal degree. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyStalk_isZero (n : ℕ) (hn : n ≠ 2 * Module.finrank ℂ F) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ n).stalk (f x)) :=
  (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology_isZero F n hn).of_iso (P.normalStalkCohomologyIso n).symm

include P in
/-- In particular, every degree below the real normal dimension vanishes. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyStalk_isZero_of_lt (n : ℕ)
    (hn : n < 2 * Module.finrank ℂ F) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ n).stalk (f x)) :=
  P.relativeCohomologyStalk_isZero n (Nat.ne_of_lt hn)

end

end OAI.AlgebraicGeometry
