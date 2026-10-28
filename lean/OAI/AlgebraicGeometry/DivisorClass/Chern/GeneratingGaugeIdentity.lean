import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingComparisonCover
import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingScalarGauge

/-! # Generating Gauge Identity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingGaugeIdentity

noncomputable section

/-! The actual algebraic transitions are gauge equivalent to the inverses of the original holomorphic transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) {n : ℕ}
  (s : Fin (n + 1) → HolomorphicSection.Data.HolomorphicLineSection u ⊤)
  (hs : ∀ x : V.analyticSpace, ∃ j, HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt u (s j) x)
  (g : V.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)
  (hg : ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = HolomorphicSection.SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs x)

include hg in
theorem generatingChernGauge_transition (a b : GeneratingComparisonCover.GeneratingChernCoverIndex V u g)
    (x : V.analyticSpace) (ha : x ∈ GeneratingComparisonCover.generatingChernComparisonCover V u g a)
    (hb : x ∈ GeneratingComparisonCover.generatingChernComparisonCover V u g b) :
    (GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).pointTransition
        ((GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).logParent a.1)
        ((GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g).logParent b.1) x
        ((GeneratingComparisonCover.generatingChernComparisonCover_mixed V u g a ha).1)
        ((GeneratingComparisonCover.generatingChernComparisonCover_mixed V u g b hb).1) =
      ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u a.2.1.2.val b.2.1.2.val).val
        ⟨x, GeneratingComparisonCover.generatingChernComparisonCover_frame V u g a ha,
          GeneratingComparisonCover.generatingChernComparisonCover_frame V u g b hb⟩)⁻¹ *
        GeneratingComparisonCover.generatingChernGauge V u s g b ⟨x, hb⟩ / GeneratingComparisonCover.generatingChernGauge V u s g a ⟨x, ha⟩ := by
  let A := GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g
  let L := GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g
  have hfa := GeneratingComparisonCover.generatingChernComparisonCover_frame V u g a ha
  have hfb := GeneratingComparisonCover.generatingChernComparisonCover_frame V u g b hb
  have hma := GeneratingComparisonCover.generatingChernComparisonCover_mixed V u g a ha
  have hmb := GeneratingComparisonCover.generatingChernComparisonCover_mixed V u g b hb
  let t := (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u a.2.1.2.val b.2.1.2.val).val
    ⟨x, hfa, hfb⟩
  let va := GeneratingComparisonCover.generatingChernSectionValue V u s g a ⟨x, ha⟩
  let vb := (s b.2.2).val a.2.1.2.val ⟨x, trivial, hfa⟩
  let ma := GeneratingComparisonCover.generatingChernMixedValue V u g a ⟨x, ha⟩
  let mb := GeneratingComparisonCover.generatingChernMixedValue V u g b ⟨x, hb⟩
  let c := L.pointTransition (L.logParent a.1) (L.logParent b.1) x hma.1 hmb.1
  have hmix := A.mixedPointTransition_gauge (L.logParent a.1) (L.logParent b.1) a.2.2 b.2.2
    x hma.1 hmb.1 hma.2 hmb.2
  have hratio := GeneratingHolomorphicTransitions.generatingAlgebraicFrame_holomorphic_transition V u s hs g hg a.2.2 b.2.2
    a.2.1.2.val ⟨x, hfa⟩ hma.2 hmb.2
  have he : c * mb / ma = vb / va := hmix.symm.trans hratio
  have ht : t ≠ 0 := Holomorphic.SlitLog.holomorphicUnit_value_ne_zero
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u a.2.1.2.val b.2.1.2.val) _
  have H := GeneratingScalarGauge.generatingChern_scalar_gauge t va vb ma mb c ht
    (GeneratingComparisonCover.generatingChernSectionValue_ne_zero V u s g hs hg a ⟨x, ha⟩)
    (GeneratingComparisonCover.generatingChernMixedValue_ne_zero V u g a ⟨x, ha⟩)
    (GeneratingComparisonCover.generatingChernMixedValue_ne_zero V u g b ⟨x, hb⟩) he
  change c = t⁻¹ * ((s b.2.2).val b.2.1.2.val ⟨x, trivial, hfb⟩ / mb) / (va / ma)
  rw [(s b.2.2).property a.2.1.2.val b.2.1.2.val x trivial hfa hfb]
  exact H

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingGaugeIdentity
