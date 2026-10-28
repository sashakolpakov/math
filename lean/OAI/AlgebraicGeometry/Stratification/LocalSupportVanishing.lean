/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicGeometry.Cycle.ComponentSingularGe
import OAI.AlgebraicGeometry.Cycle.SmoothPairOpenTransport
import OAI.AlgebraicGeometry.Cycle.TransportCohomologySection
import OAI.AlgebraicTopology.Sheaf.OpenRestrictedVanishing

/-! # Local Support Vanishing -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Local support vanishing on canonical singular-filtration layers

Every point of a smooth layer has a fixed-dimensional affine source neighborhood, of
dimension strictly less than that of the original cycle component. Deleting the image of
the discarded source complement makes that neighborhood closed in a smaller ambient open,
and normal neighborhoods there transport to the original projective ambient space and its
fixed supported injective resolution. The local lower vanishing follows from those maps
and the dimension bounds.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace

open OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p) (k : ℕ)

include hx in
/-- Every point in the `k`th layer has cofinal ambient neighborhoods
whose relative cohomology below degree `2(p+1)` vanishes. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayer_exists_relativeCohomology_vanishing
    (y : ComplexPoint.Basic.ComplexSchemePoint X)
    (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k)
    (hyNext : y ∉ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1))
    (V : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), W ≤ V ∧
      W ≤ (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl ∧
      y ∈ W ∧ ∀ n : ℕ, n < 2 * (p + 1) →
        IsZero (ModuleCat.of ℚ (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set (ComplexPoint.Basic.ComplexSchemePoint X))
            (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint.Basic.ComplexSchemePoint X))) n)) := by
  obtain ⟨z, rfl⟩ := (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_layer X x k).ge ⟨hy, hyNext⟩
  let O := Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k
  let OX := Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver X x k
  let Y := Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOver X x k
  let i : Y ⟶ OX := Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLiftOver X x k
  obtain ⟨A, hA, hzA, m, hm, hcodim, hdim⟩ :=
    Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension
      X x hx k z.underlying
  let : SmoothOfRelativeDimension m (ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A).hom := hdim
  let zA := ComplexPoint.Basic.ComplexSchemePoint.asOpenPoint Y A z hzA
  let f := ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X O)
  have hS : f ⁻¹'
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint.Basic.ComplexSchemePoint X)) =
        Set.range (ComplexPoint.Basic.Point.map i) :=
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularStratumClosedLift_complexPoints_range X x k).symm
  have he : f (ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) zA) =
      ComplexPoint.Basic.Point.map (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOverι X x k) z := by
    apply Over.OverMorphism.ext
    change (zA.left ≫ (A.ι ≫ Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k)) ≫ O.ι =
      z.left ≫ Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k
    rw [Category.assoc, Category.assoc, Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_ι,
      ← Category.assoc]
    exact congrArg (fun g => g ≫ Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k)
      (ComplexPoint.Basic.ComplexSchemePoint.liftToOpen_fac Y A z hzA)
  let V' := V ⊓ (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl
  have hzV' : f (ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) zA) ∈ V' := by
    rw [he]
    exact ⟨hyV, hyNext⟩
  have : SmoothOfRelativeDimension (Topology.Dimension.Basic.TopologicalSpace.dim X.left) OX.hom := by
    change SmoothOfRelativeDimension (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (Topology.Dimension.Basic.TopologicalSpace.dim X.left) O.ι X.hom
  obtain ⟨W, hWV', hzW, hW⟩ := ComplexPoint.Basic.ComplexSchemePoint.exists_smoothClosedSourceOpenImageNeighborhood
    OX Y i m (Topology.Dimension.Basic.TopologicalSpace.dim X.left) f (ComplexPoint.Basic.ComplexSchemePoint.isOpenEmbedding_map_open X O)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint.Basic.ComplexSchemePoint X))
    hS A zA V' hzV'
  exact ⟨W, hWV'.trans inf_le_left, hWV'.trans inf_le_right, he ▸ hzW,
    fun n hn ↦ hW n (by omega)⟩

include hx in
/-- The original ambient supported injective complex has cofinally vanishing section
cohomology below `2(p+1)` at every point outside the next closed support. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1))
    (y : ComplexPoint.Basic.ComplexSchemePoint X)
    (hyNext : y ∉ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1))
    (V : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), W ≤ V ∧ y ∈ W ∧
      IsZero ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) W).mapHomologicalComplex
        ℤᵘᵖ).obj (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
          (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) V).map_isZero
      ((ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k
    · obtain ⟨W, hWV, _, hyW, hW⟩ :=
        ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayer_exists_relativeCohomology_vanishing X x hx k
          y hy hyNext V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set (ComplexPoint.Basic.ComplexSchemePoint X))
            (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint.Basic.ComplexSchemePoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k) W q
      let : Subsingleton ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) W).mapHomologicalComplex ℤᵘᵖ).obj
            (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
              (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k))).homology (q : ℤ)) :=
        e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact AlgebraicTopology.Support.SectionRestrictionIs.TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k).compl W
        ((ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

include hx in
/-- The open-layer section complex needed by finite support localization has zero cohomology
below `2(p+1)`. The resolution remains the one on the original projective ambient variety. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayerSectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl).mapHomologicalComplex
        ℤᵘᵖ).obj (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
          (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  apply AlgebraicTopology.Sheaf.OpenRestrictedVanishing.TopCat.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) _ _ 0 n
  · exact fun j ↦ AlgebraicTopology.Support.FlasqueSections.TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k).compl
      ((ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy V hyV ↦
      ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
        X x hx k j (hj.trans_lt hn) y hy V hyV

end

end OAI.AlgebraicGeometry
