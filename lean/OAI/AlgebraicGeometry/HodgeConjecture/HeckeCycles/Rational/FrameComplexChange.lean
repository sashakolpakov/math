import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PhaseMatrixReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RingSymplecticPairing

/-! # Frame Complex Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameComplexChange.CM

noncomputable section

/-! Complexify a proved rational symplectic change of coordinates, with
the exact exchange and relabeling of its native phase coordinates. -/

open scoped Classical _root_.Matrix

variable {I J U V : Type} [Fintype I] [DecidableEq I]
  [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℂ V]

def swap (e : I ≃ J) : ((J ⊕ J) → ℂ) ≃ₗ[ℂ] ((I ⊕ I) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ ((Equiv.sumCongr e e).trans (Equiv.sumComm J J))

def frame (e : I ≃ J) (c : V ≃ₗ[ℂ] ((I ⊕ I) → ℂ)) (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) :
    V ≃ₗ[ℂ] ((J ⊕ J) → ℂ) :=
  (c.trans (RingSymplecticPairing.CM.linearEquiv (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℂ) S))).trans
    (swap e).symm

variable (e : I ≃ J) (q : U ≃ₗ[ℚ] ((I ⊕ I) → ℚ))
  (c : V ≃ₗ[ℂ] ((I ⊕ I) → ℂ)) (r : U → V)
  (hr : ∀ x, c (r x) = fun i => (q x i : ℂ))
  (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (p : U → ((J ⊕ J) → ℚ))
  (hS : ∀ x, S.val *ᵥ q x = PhaseMatrixReindex.CM.swap e (p x))

include hr hS in
theorem rational (x : U) : frame e c S (r x) = fun j => (p x j : ℂ) := by
  apply (swap e).injective
  change swap e ((swap e).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change S.val.map (algebraMap ℚ ℂ) *ᵥ c (r x) = _
  rw [hr]
  funext i
  have h := (RingHom.map_mulVec (algebraMap ℚ ℂ) S.val (q x) i).symm.trans
    (congrArg (algebraMap ℚ ℂ) (congrFun (hS x) i))
  cases i <;> exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameComplexChange.CM
