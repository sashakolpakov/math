import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingHolomorphicTransitions
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Singular

/-! # Generating Comparison Cover -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingComparisonCover

noncomputable section

section

/-! An actual common cover for the original holomorphic logarithms, algebraic logarithms, and generating section frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) {n : ℕ}
  (g : V.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)

abbrev GeneratingChernCoverIndex :=
  (GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).LogCoverIndex ×
    Holomorphic.Singular.HolomorphicLogIndex V.analyticModel V.analyticSpace u × Fin (n + 1)

def generatingChernComparisonCover (a : GeneratingChernCoverIndex V u g) : Opens V.analyticSpace :=
  ((GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).logCover a.1 ⊓
    Holomorphic.Singular.holomorphicLogCover V.analyticModel V.analyticSpace u a.2.1) ⊓
    (GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).analyticDomain a.2.2

theorem generatingChernComparisonCover_algebraic (a : GeneratingChernCoverIndex V u g) :
    generatingChernComparisonCover V u g a ≤
      (GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).logCover a.1 :=
  inf_le_left.trans inf_le_left

theorem generatingChernComparisonCover_holomorphic (a : GeneratingChernCoverIndex V u g) :
    generatingChernComparisonCover V u g a ≤ Holomorphic.Singular.holomorphicLogCover V.analyticModel V.analyticSpace u a.2.1 :=
  inf_le_left.trans inf_le_right

theorem generatingChernComparisonCover_generator (a : GeneratingChernCoverIndex V u g) :
    generatingChernComparisonCover V u g a ≤
      (GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).analyticDomain a.2.2 := inf_le_right

theorem generatingChernComparisonCover_frame (a : GeneratingChernCoverIndex V u g) :
    generatingChernComparisonCover V u g a ≤
      Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u a.2.1.2.val :=
  (generatingChernComparisonCover_holomorphic V u g a).trans
    (Holomorphic.Singular.holomorphicLogCover_subset V.analyticModel V.analyticSpace u a.2.1)

theorem generatingChernComparisonCover_mixed (a : GeneratingChernCoverIndex V u g) :
    generatingChernComparisonCover V u g a ≤
      (GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).analyticCover
        ((GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).logParent a.1) ⊓
      (GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).analyticDomain a.2.2 :=
  le_inf ((generatingChernComparisonCover_algebraic V u g a).trans
    ((GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).logCover_subset a.1))
    (generatingChernComparisonCover_generator V u g a)

theorem generatingChernComparisonCover_covers
    (s : Fin (n + 1) → HolomorphicSection.Data.HolomorphicLineSection u ⊤)
    (hs : ∀ x : V.analyticSpace, ∃ j, HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt u (s j) x)
    (hg : ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = HolomorphicSection.SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs x)
    (x : V.analyticSpace) : ∃ a, x ∈ generatingChernComparisonCover V u g a := by
  obtain ⟨a, ha⟩ := (GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).logCover_covers x
  obtain ⟨b, hb⟩ := Holomorphic.Singular.holomorphicLogCover_covers V.analyticModel V.analyticSpace u x
  obtain ⟨j, hj⟩ := hs x
  exact ⟨(a, b, j), ⟨ha, hb⟩, (GeneratingHolomorphicTransitions.generatingAlgebraicFrame_domain_iff V u s hs g hg j x).mpr hj⟩

end

/-! The explicit continuous, nowhere-zero gauges comparing original holomorphic and algebraic frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) {n : ℕ}
  (s : Fin (n + 1) → HolomorphicSection.Data.HolomorphicLineSection u ⊤)
  (g : V.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)

def generatingChernSectionValue (a : GeneratingChernCoverIndex V u g) :
    C(generatingChernComparisonCover V u g a, ℂ) :=
  ⟨fun x => (s a.2.2).val a.2.1.2.val
    ⟨x.val, trivial, generatingChernComparisonCover_frame V u g a x.property⟩,
    ((s a.2.2).val a.2.1.2.val).property.continuous.comp
      (continuous_subtype_val.subtype_mk (fun x =>
        ⟨trivial, generatingChernComparisonCover_frame V u g a x.property⟩))⟩

def generatingChernMixedValue (a : GeneratingChernCoverIndex V u g) :
    C(generatingChernComparisonCover V u g a, ℂ) :=
  ((GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).mixedPair
      ((GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).logParent a.1) a.2.2).comp
    (LogRefinementOpen.Construction.openInclusionMap (generatingChernComparisonCover_mixed V u g a))

theorem generatingChernMixedValue_ne_zero (a : GeneratingChernCoverIndex V u g)
    (x : generatingChernComparisonCover V u g a) : generatingChernMixedValue V u g a x ≠ 0 :=
  (GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).mixedPair_ne_zero _ _ _

def generatingChernGauge (a : GeneratingChernCoverIndex V u g) :
    C(generatingChernComparisonCover V u g a, ℂ) :=
  ⟨fun x => generatingChernSectionValue V u s g a x / generatingChernMixedValue V u g a x,
    (generatingChernSectionValue V u s g a).continuous.div
      (generatingChernMixedValue V u g a).continuous (generatingChernMixedValue_ne_zero V u g a)⟩

theorem generatingChernSectionValue_ne_zero
    (hs : ∀ x : V.analyticSpace, ∃ j, HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt u (s j) x)
    (hg : ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = HolomorphicSection.SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs x)
    (a : GeneratingChernCoverIndex V u g) (x : generatingChernComparisonCover V u g a) :
    generatingChernSectionValue V u s g a x ≠ 0 := by
  exact (HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt_iff_frame u (s a.2.2) a.2.1.2.val x.val
    (generatingChernComparisonCover_frame V u g a x.property)).mp
    ((GeneratingHolomorphicTransitions.generatingAlgebraicFrame_domain_iff V u s hs g hg a.2.2 x.val).mp
      (generatingChernComparisonCover_generator V u g a x.property))

theorem generatingChernGauge_ne_zero
    (hs : ∀ x : V.analyticSpace, ∃ j, HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt u (s j) x)
    (hg : ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = HolomorphicSection.SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs x)
    (a : GeneratingChernCoverIndex V u g) (x : generatingChernComparisonCover V u g a) :
    generatingChernGauge V u s g a x ≠ 0 :=
  div_ne_zero (generatingChernSectionValue_ne_zero V u s g hs hg a x)
    (generatingChernMixedValue_ne_zero V u g a x)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingComparisonCover
