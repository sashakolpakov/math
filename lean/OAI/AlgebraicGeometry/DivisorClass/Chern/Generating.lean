import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingGaugeIdentity
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech
import OAI.AlgebraicGeometry.DivisorClass.Chern.Iso

/-! # Generating -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Generating

noncomputable section

/-! Exact comparison of the original algebraic first Chern class with the original holomorphic Chern class of the generating section bundle. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The sign follows from the original algebraic generator-transition convention
and the original holomorphic coordinate-transition convention. -/
theorem generatingAlgebraicLineBundle_firstChern (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) {n : ℕ}
    (s : Fin (n + 1) → HolomorphicSection.Data.HolomorphicLineSection u ⊤)
    (hs : ∀ x : V.analyticSpace, ∃ j, HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt u (s j) x)
    (g : V.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)
    (hg : ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = HolomorphicSection.SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs x) :
    First.firstChernClassQ V.presentation (GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g) =
      -Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u := by
  let T := TopCat.of V.analyticSpace
  let L := GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g
  let U := GeneratingComparisonCover.generatingChernComparisonCover V u g
  have hU := GeneratingComparisonCover.generatingChernComparisonCover_covers V u g s hs hg
  let rH : GeneratingComparisonCover.GeneratingChernCoverIndex V u g → Holomorphic.Singular.HolomorphicLogIndex V.analyticModel V.analyticSpace u :=
    fun a => a.2.1
  let rA : GeneratingComparisonCover.GeneratingChernCoverIndex V u g → L.LogCoverIndex := Prod.fst
  have hHU := GeneratingComparisonCover.generatingChernComparisonCover_holomorphic V u g
  have hAU := GeneratingComparisonCover.generatingChernComparisonCover_algebraic V u g
  let lH := LogRefinement.RationalCech.refineLogCech T (Holomorphic.Singular.holomorphicLogCover V.analyticModel V.analyticSpace u) U rH hHU
    (Holomorphic.Singular.holomorphicLogCech V.analyticModel V.analyticSpace u)
  let lA := LogRefinement.RationalCech.refineLogCech T L.logCover U rA hAU L.bundleLogCech
  have hH := LogRefinement.RationalCech.exponentialCocycle_refinement T (Holomorphic.Singular.holomorphicLogCover V.analyticModel V.analyticSpace u)
    U rH hHU (Holomorphic.Singular.holomorphicLogCech V.analyticModel V.analyticSpace u)
    (Holomorphic.Singular.holomorphicLogCech_cocycle V.analyticModel V.analyticSpace u)
  have hA := LogRefinement.RationalCech.exponentialCocycle_refinement T L.logCover U rA hAU L.bundleLogCech L.bundleLogCech_cocycle
  have hN := LogCech.RationalCech.exponentialCocycle_neg T U lH hH
  have hc : LogCech.RationalCech.logarithmicSingularClass T U hU lA hA = LogCech.RationalCech.logarithmicSingularClass T U hU (-lH) hN := by
    apply ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge T U (GeneratingComparisonCover.generatingChernGauge V u s g)
      (GeneratingComparisonCover.generatingChernGauge_ne_zero V u s g hs hg) hU (-lH) lA hN hA
    intro a p
    have hla := L.bundleLogCech_exp_point (rA ∘ a)
      ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le L.logCover U rA hAU a p.property⟩
    have hlh := Holomorphic.Singular.exp_holomorphicLogCech V.analyticModel V.analyticSpace u (rH ∘ a)
      ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le
        (Holomorphic.Singular.holomorphicLogCover V.analyticModel V.analyticSpace u) U rH hHU a p.property⟩
    have hln : Complex.exp ((-lH) a p) =
        ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u
          (a 0).2.1.2.val (a 1).2.1.2.val).val
          ⟨p.val, GeneratingComparisonCover.generatingChernComparisonCover_frame V u g (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property),
            GeneratingComparisonCover.generatingChernComparisonCover_frame V u g (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)⟩)⁻¹ := by
      change Complex.exp (-lH a p) = _
      rw [Complex.exp_neg]
      exact congrArg Inv.inv hlh
    rw [hln]
    exact hla.trans (GeneratingGaugeIdentity.generatingChernGauge_transition V u s hs g hg (a 0) (a 1) p.val
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))
  have hRA := LogRefinement.RationalCech.logarithmicSingularClass_refinement T L.logCover U rA hAU L.logCover_covers hU
    L.bundleLogCech L.bundleLogCech_cocycle
  have hRH := LogRefinement.RationalCech.logarithmicSingularClass_refinement T
    (Holomorphic.Singular.holomorphicLogCover V.analyticModel V.analyticSpace u) U rH hHU
    (Holomorphic.Singular.holomorphicLogCover_covers V.analyticModel V.analyticSpace u) hU
    (Holomorphic.Singular.holomorphicLogCech V.analyticModel V.analyticSpace u) (Holomorphic.Singular.holomorphicLogCech_cocycle V.analyticModel V.analyticSpace u)
  exact hRA.symm.trans (hc.trans ((LogCech.RationalCech.logarithmicSingularClass_neg T U hU lH hH).trans
    (congrArg Neg.neg hRH)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Generating
