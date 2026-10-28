import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalNaturality
import OAI.Analysis.DifferentialForms.Manifold.Bidegree

/-! # Vector Cauchy -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.VectorCauchy.Dolbeault

noncomputable section

/-! The actual localized vector Cauchy integral preserves each pure
bidegree, using the kernels of the original scalar-character operators. -/

open Set
open scoped ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

def scalarCovectorPullbackCLM (n : ℕ) (z : ℂ) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n where
  toLinearMap := Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n z
  cont := (ContinuousAlternatingMap.compContinuousLinearMapCLM
    (ContinuousLinearMap.lsmul ℝ ℂ z)).continuous

@[simp] theorem scalarCovectorPullbackCLM_apply (n : ℕ) (z : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    scalarCovectorPullbackCLM n z a = Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E n z a := rfl

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem localizedVectorCauchyTransform_pure (p q : ℕ) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q)} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hsub : tsupport χ ⊆ U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    (x : P × ℂ) (hx : x.1 ∈ S) (hpure : ∀ w ∈ U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (g x.1 w)) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ g x) := by
  intro z v
  let L : Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q) →L[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q) :=
    scalarCovectorPullbackCLM (p + q) z -
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z • ContinuousLinearMap.id ℂ (Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q))
  have hzero : ∀ w ∈ U, L (g x.1 w) = 0 := by
    intro w hw
    ext u
    change g x.1 w (fun i => (z : ℂ) • u i) -
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * g x.1 w u = 0
    rw [hpure w hw z u, sub_self]
  have h := VectorCauchyLocalNaturality.Dolbeault.localizedVectorCauchyTransform_kernel L hχ hc hS hU hsub hg x hx hzero
  have hv := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q) => a v) h
  change VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ g x (fun i => (z : ℂ) • v i) -
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ g x v = 0 at hv
  exact sub_eq_zero.mp hv

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.VectorCauchy.Dolbeault
