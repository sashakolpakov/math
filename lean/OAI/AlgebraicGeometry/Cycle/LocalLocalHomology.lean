/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ClosedImmersion.NormalCoordinatesAt
import OAI.AlgebraicGeometry.Cycle.LocalPurityOf
import OAI.AlgebraicTopology.LocalHomology.FlattenedSupport
import OAI.AlgebraicTopology.Singular.RelativeCochainG

/-! # Local Local Homology -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Local relative homology for smooth closed supports

Every prescribed open neighborhood of a point on a smooth closed complex subvariety contains
a smaller open neighborhood whose support-complement pair has rational
relative homology and cohomology only in degree twice the complex codimension. The comparison
and the exactly normalized normal class come from flattening, radial compression, and tangent
contraction.

This is a cofinal local singular calculation. The identification with derived sheaf sections
with support, and gluing its normalizations across overlapping charts, are separate theorems.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y)
  (V : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) (hzV : ComplexPoint.Basic.Point.map i z ∈ V)

/-- Let `i: Y → X` be a closed immersion of smooth schemes over `ℂ` of dimensions `m` and `d`,
respectively. For `z ∈ Y(ℂ)` and an ambient open `V ⊆ X(ℂ)`, this is the chart at `i(z)` with
source restricted to `V`. Its coordinates lie in `ℂ^m × ℂ^{d-m}`, and the image of `Y(ℂ)` is
given by vanishing of the second coordinate. -/
def ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart :
    OpenPartialHomeomorph (ComplexPoint.Basic.ComplexSchemePoint X)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).restrOpen V V.isOpen

include hzV in
theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_source :
    ComplexPoint.Basic.Point.map i z ∈
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V).source :=
  ⟨ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_source X Y i m d z, hzV⟩

@[simp] theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_center :
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V (ComplexPoint.Basic.Point.map i z) =
      (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) :=
  ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_center X Y i m d z

theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_range_iff (y : ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V).source) :
    y ∈ Set.range (ComplexPoint.Basic.Point.map i) ↔
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V y).2 = 0 :=
  ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_mem_range_iff X Y i m d z y hy.1

/-- A small open support-model neighborhood inside the prescribed open. -/
def ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood : Opens (ComplexPoint.Basic.ComplexSchemePoint X) :=
  AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood (Fin m → ℂ) (d - m)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V)
    (ComplexPoint.Basic.Point.map i z)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)

theorem ComplexPoint.Basic.ComplexSchemePoint.mem_smoothClosedSupportNeighborhood :
    ComplexPoint.Basic.Point.map i z ∈ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood X Y i m d z V hzV :=
  AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.mem_flattenedSupportNeighborhood _ _ _ _ _

theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood_le :
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood X Y i m d z V hzV ≤ V :=
  fun _ hy ↦ (AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportNeighborhood_subset_source (Fin m → ℂ) (d - m)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V)
    (ComplexPoint.Basic.Point.map i z)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)
    hy).2

/-- The local support-complement pair, with the image as support. -/
abbrev ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair : TopPair :=
  AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood X Y i m d z V hzV)
    (Set.range (ComplexPoint.Basic.Point.map i))

/-- The pair homeomorphism to the product normal model. -/
def ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPairIso :
    AlgebraicTopology.LocalHomology.NormalSlicePurity.Singular.normalSlicePair (Fin m → ℂ) (d - m) ≅
      ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV :=
  AlgebraicTopology.LocalHomology.FlattenedSupport.Singular.flattenedSupportPairIso (Fin m → ℂ) (d - m)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart X Y i m d z V)
    (ComplexPoint.Basic.Point.map i z)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)
    (Set.range (ComplexPoint.Basic.Point.map i))
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
    (congrArg Prod.snd (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRestrictionChart_center X Y i m d z V))

/-- All-degree local relative homology, computed from the pair maps. -/
def ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n ≅
        AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ (d - m)) n :=
  ((AlgebraicTopology.Singular.Cohomology.relativeHomologyFunctor ℚ n).mapIso
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPairIso X Y i m d z V hzV).symm) ≪≫
    AlgebraicTopology.LocalHomology.NormalSlicePurity.Singular.normalSliceRelativeHomologyIso (Fin m → ℂ) (d - m) n

theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero (AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n) :=
  (ComplexPoint.LocalHomologyVanishing.AlgebraicTopology.Singular.standardComplexLocalHomology_isZero_of_ne (d - m) n hn).of_iso
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV n)

/-- The exact complex-normal class in the local support pair. -/
def ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass :
    AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) (2 * (d - m)) :=
  (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
    (2 * (d - m))).inv.hom (AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ (d - m))

@[simp] theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass_normalization :
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
      (2 * (d - m))).hom.hom
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass X Y i m d z V hzV) =
        AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ (d - m) :=
  ConcreteCategory.congr_hom
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
      (2 * (d - m))).inv_hom_id _

theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass_ne_zero :
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass X Y i m d z V hzV ≠ 0 := by
  intro hzero
  have h := ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass_normalization X Y i m d z V hzV
  rw [hzero, map_zero] at h
  exact AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator.Singular.standardComplexLocalClass_ne_zero_for_chart (d - m) h.symm

/-- The coclass normalized to pair to one with the exact complex normal class. -/
def ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalCoclass :
    AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV)
        (2 * (d - m)) :=
  Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedRelativeCoclass (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass X Y i m d z V hzV)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass_ne_zero X Y i m d z V hzV)

@[simp] theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalCoclass_apply_class :
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology ℚ
        (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) (2 * (d - m))
        (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalCoclass X Y i m d z V hzV)
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNormalClass X Y i m d z V hzV) = 1 :=
  Cycle.LocalPurityOf.AlgebraicTopology.Singular.normalizedRelativeCoclass_pairing_self _ _

theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeCohomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n) :=
  AlgebraicTopology.Singular.CohomologyTo.relativeCohomology_isZero ℚ _ n
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeHomology_isZero_of_ne X Y i m d z V hzV n hn)

end

end OAI.AlgebraicGeometry
