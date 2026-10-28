import OAI.AlgebraicGeometry.DivisorClass.Chern.LogGauge
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinement
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.Logarithms
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen

/-! # Continuous Gauge -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge

noncomputable section

/-!
# ChernClass: invariance under arbitrary continuous changes of frame

No global logarithm of a change of frame is assumed. Local logarithms are
constructed on a refinement, where logarithmic gauge invariance applies.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (U : I → Opens X)
variable (g : ∀ i, C(U i, ℂ)) (hg : ∀ i x, g i x ≠ 0)

/-- Local logarithms of a continuous change of frame, as a degree-zero cochain. -/
def sectionLogCech : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X)
    (Open.Logarithms.Construction.sectionLogRefinement U g hg).cover 0 :=
  fun a => ((Open.Logarithms.Construction.sectionLogRefinement U g hg).logarithm (a 0)).comp
    (LogRefinementOpen.Construction.openInclusionMap (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (Open.Logarithms.Construction.sectionLogRefinement U g hg).cover a 0))

theorem sectionLogCech_exp (a : Fin 1 → Σ i, U i)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (Open.Logarithms.Construction.sectionLogRefinement U g hg).cover a) :
    Complex.exp (sectionLogCech X U g hg a x) =
      g (a 0).1 ⟨x.val, (Open.Logarithms.Construction.sectionLogRefinement U g hg).subset (a 0)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (Open.Logarithms.Construction.sectionLogRefinement U g hg).cover a 0 x.property)⟩ :=
  (Open.Logarithms.Construction.sectionLogRefinement U g hg).exp_logarithm (a 0) _

/-- The exponential of the logarithmic coboundary is the ratio of frame changes. -/
theorem sectionLogCech_delta_exp (a : Fin 2 → Σ i, U i)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (Open.Logarithms.Construction.sectionLogRefinement U g hg).cover a) :
    Complex.exp (Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X)
        (Open.Logarithms.Construction.sectionLogRefinement U g hg).cover 0 (sectionLogCech X U g hg) a x) =
      g (a 1).1 ⟨x.val, (Open.Logarithms.Construction.sectionLogRefinement U g hg).subset (a 1)
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (Open.Logarithms.Construction.sectionLogRefinement U g hg).cover a 1 x.property)⟩ /
        g (a 0).1 ⟨x.val, (Open.Logarithms.Construction.sectionLogRefinement U g hg).subset (a 0)
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (Open.Logarithms.Construction.sectionLogRefinement U g hg).cover a 0 x.property)⟩ := by
  rw [Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two]
  change Complex.exp ((1 : ℤ) • sectionLogCech X U g hg (a ∘ (0 : Fin 2).succAbove) _ +
    (-1 : ℤ) • sectionLogCech X U g hg (a ∘ (1 : Fin 2).succAbove) _) = _
  rw [one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, Complex.exp_sub,
    sectionLogCech_exp, sectionLogCech_exp]
  rfl

include hg in
/-- Arbitrary nowhere-zero continuous changes of frame preserve the class. -/
theorem logarithmicSingularClass_continuous_gauge
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l l' : LogCech.RationalCech.LogCechCochain X U) (h : LogCech.RationalCech.ExponentialCocycle X U l)
    (h' : LogCech.RationalCech.ExponentialCocycle X U l')
    (he : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l' a x) = Complex.exp (l a x) *
        g (a 1) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
          g (a 0) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩) :
    LogCech.RationalCech.logarithmicSingularClass X U hU l' h' = LogCech.RationalCech.logarithmicSingularClass X U hU l h := by
  let R := Open.Logarithms.Construction.sectionLogRefinement U g hg
  let r : (Σ i, U i) → I := Sigma.fst
  have hr : ∀ a, R.cover a ≤ U (r a) := R.subset
  have hV : ∀ x, ∃ a, x ∈ R.cover a := Open.Logarithms.Construction.sectionLogRefinement_covers U g hg hU
  let k := LogRefinement.RationalCech.refineLogCech X U R.cover r hr l
  let k' := LogRefinement.RationalCech.refineLogCech X U R.cover r hr l'
  have hk := LogRefinement.RationalCech.exponentialCocycle_refinement X U R.cover r hr l h
  have hk' := LogRefinement.RationalCech.exponentialCocycle_refinement X U R.cover r hr l' h'
  have hk_eq : LogCech.RationalCech.logarithmicSingularClass X R.cover hV k' hk' =
      LogCech.RationalCech.logarithmicSingularClass X R.cover hV k hk := by
    apply LogGauge.RationalCech.logarithmicSingularClass_gauge_of_exp_eq X R.cover hV k k' hk hk'
      (sectionLogCech X U g hg)
    intro a x
    change Complex.exp (l' (r ∘ a) _) = Complex.exp
      (l (r ∘ a) _ + Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) R.cover 0
        (sectionLogCech X U g hg) a x)
    rw [Complex.exp_add, sectionLogCech_delta_exp, ← mul_div_assoc]
    exact he (r ∘ a) ⟨x.val, Rational.Cech.RationalCech.cechIntersection_refinement_le U R.cover r hr a x.property⟩
  exact (LogRefinement.RationalCech.logarithmicSingularClass_refinement X U R.cover r hr hU hV l' h').symm.trans
    (hk_eq.trans (LogRefinement.RationalCech.logarithmicSingularClass_refinement X U R.cover r hr hU hV l h))

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge
