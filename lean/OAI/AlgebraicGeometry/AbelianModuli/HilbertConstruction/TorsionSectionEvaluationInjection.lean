import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GraphTorsionSectionDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.LineBundleEvaluation

/-! # Torsion Section Evaluation Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! At a sufficiently high full level, simultaneous evaluation is an
injective linear map on the actual graph-power section space. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g N n : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

def PolarizationData.PolarizedAbelianWithFullLevel.fullLevelEvenGraphEvaluation (level : A.abelian.FullLevel n) (t : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj (A.graphBundle.tensorPower (2 * t)).sheaf →ₗ[K]
      (Multiplicative (Fin (2 * g) → ZMod n) → K) :=
  LinearMap.pi (fun c => Rational.LineBundleEvaluation.rationalLineBundleEvaluation A.abelian.scheme.hom
    (A.graphBundle.tensorPower (2 * t)) ((A.abelian.fullLevelRationalTorsionEquiv level).symm c).val.left
    ((A.abelian.fullLevelRationalTorsionEquiv level).symm c).val.w)

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelEvenGraphEvaluation_injective [IsAlgClosed K] [NeZero n]
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t) (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
    (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2) :
    Function.Injective (A.fullLevelEvenGraphEvaluation level t) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have hz : A.fullLevelEvenGraphEvaluation level t v = 0 := hv
  let L := A.graphBundle.tensorPower (2 * t)
  let e := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) L.sheaf
  have ha : e.symm v = 0 := by
    apply A.evenGraphPower_section_eq_zero_of_fullLevel_vanishing hg hδ hN hNk t ht htlarge level hlarge
    intro c
    apply (Rational.LineBundleEvaluation.rationalLineBundleEvaluation_eq_zero A.abelian.scheme.hom L
      ((A.abelian.fullLevelRationalTorsionEquiv level).symm c).val.left
      ((A.abelian.fullLevelRationalTorsionEquiv level).symm c).val.w v).mp
    exact congrFun hz c
  change v = 0
  have h := congrArg e ha
  exact (e.apply_symm_apply v).symm.trans (h.trans (map_zero e))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
