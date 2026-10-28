import OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoPurity
import OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology

/-! # Codimension Two Removal -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoRemoval

noncomputable section

/-!
# ChernClass: actual degree-two restriction across higher-codimension subsets

The two obstruction groups vanish by the actual stratification purity
theorem. Hence both absolute and supported degree-two restriction are
isomorphisms. A neighborhood of every codimension-one point, together with
the reference open, has exactly such an ignorable closed complement.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Construction

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (F : Closeds X.carrier) (hF : ∀ z ∈ F, 1 < Order.coheight z)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)

include hF in
/-- The actual global obstruction groups vanish below degree four. -/
theorem codimensionTwo_cohomology_isZero (n : ℕ) (hn : n < 4) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl : Set T) n) :=
  (CodimensionTwoPurity.Construction.codimensionTwo_open_cohomology_isZero X F hF ⊤ n hn).of_iso
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) T (Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl : Set T) n).symm

include hF in
/-- Ordinary degree-two cohomology is unchanged by removing this actual
closed algebraic subset. -/
theorem codimensionTwo_absoluteRestriction_isIso :
    IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) T (Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl : Set T) 2) :=
  AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology.subspaceCohomologyRestriction_isIso_of_relative_zero
    (ModuleCat.of ℚ ℚ) T (Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl : Set T) 2
    (codimensionTwo_cohomology_isZero X F hF 2 (by decide))
    (codimensionTwo_cohomology_isZero X F hF 3 (by decide))

include hF in
/-- Restriction of supported degree-two cohomology is also the actual
triple-sequence isomorphism. -/
theorem codimensionTwo_relativeRestriction_isIso (B : Set T)
    (hB : B ⊆ Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl) :
    IsIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T B (Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl) 2) :=
  CycleClass.Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction_isIso (ModuleCat.of ℚ ℚ) T
    (Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl : Set T) B hB 2
    (codimensionTwo_cohomology_isZero X F hF 2 (by decide))
    (codimensionTwo_cohomology_isZero X F hF 3 (by decide))

include hF in
theorem codimensionTwo_relative_eq_iff (B : Set T) (hB : B ⊆ Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T B 2) :
    a = b ↔
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T B (Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl) 2 a =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T B (Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl) 2 b := by
  have := codimensionTwo_relativeRestriction_isIso X F hF B hB
  exact ((ModuleCat.mono_iff_injective _).mp inferInstance).eq_iff.symm

/-- Missing a nonempty open forces positive specialization codimension. -/
theorem one_le_coheight_of_not_mem (R : X.carrier.Opens) [Nonempty R]
    (z : X.carrier) (hz : z ∉ R) : 1 ≤ Order.coheight z := by
  let Z : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm z
  let W : IrreducibleCloseds X.carrier :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.carrier, isClosed_univ⟩
  have hZ : (Z : Set X.carrier) ⊆ (R : Set X.carrier)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hz) R.isOpen.isClosed_compl
  have hZW : Z < W := by
    apply lt_of_le_not_ge (Set.subset_univ _)
    intro hWZ
    obtain ⟨y⟩ := ‹Nonempty R›
    exact hZ (hWZ (Set.mem_univ y.val)) y.property
  have hc : 1 ≤ Order.coheight Z :=
    (show (1 : ℕ∞) ≤ Order.coheight W + 1 from le_add_self).trans
      (Order.coheight_add_one_le hZW)
  simpa only [Z, Order.coheight_orderIso] using hc

/-- Neighborhoods of every actual codimension-one point leave only a
closed subset of codimension at least two outside the reference open. -/
theorem complement_comparisonOpen_coheight
    (R : X.carrier.Opens) [Nonempty R]
    (U : {z : X.carrier // Order.coheight z = 1} → X.carrier.Opens)
    (hU : ∀ z, z.val ∈ U z) :
    ∀ z ∈ (R ⊔ iSup U).compl, 1 < Order.coheight z := by
  intro z hz
  have hzR : z ∉ R := fun h => hz (Or.inl h)
  have h1 := one_le_coheight_of_not_mem X R z hzR
  apply lt_of_le_of_ne h1
  intro he
  exact hz (Or.inr (Opens.mem_iSup.mpr ⟨⟨z, he.symm⟩, hU ⟨z, he.symm⟩⟩))

end Construction

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoRemoval
