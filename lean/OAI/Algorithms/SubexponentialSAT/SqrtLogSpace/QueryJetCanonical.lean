import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation

/-! Canonical cutoff identities for immediate Boolean scalarization. These
identities retain precisely the same lifting and Taylor coefficient ranges. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog

section CanonicalSpecialization
variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- The actual scalar specialization retains exactly the source cutoffs. -/
@[simp] theorem specializeDense_canonical (t J : ℕ) (x : V → Bool)
    (f : Squarefree.Jet V R) :
    QueryEvaluation.specializeDense t J x (Squarefree.canonical t J f) =
      QueryEvaluation.specializeDense t J x f := by
  ext u z
  simp [QueryEvaluation.coeff_specializeDense, Squarefree.coeff_canonical, u.isLt, z.isLt]

/-- Immediate scalar specialization commutes with the exact two cutoffs.
This identifies the actual producer's canonical incidence denotation. -/
theorem jetScalar_eval_canonical {W : Type*} [DecidableEq W]
    (u J : ℕ) (U : V → Bool) (f : Squarefree.Jet V R) :
    Moments.jetScalar (V := W) (Moments.jetEval (Squarefree.boolValue U)
      (Squarefree.boolValue_idempotent U) (Squarefree.canonical u J f)) =
      Squarefree.canonical u J (Moments.jetScalar (V := W)
        (Moments.jetEval (Squarefree.boolValue U) (Squarefree.boolValue_idempotent U) f)) := by
  apply Polynomial.ext
  intro a
  apply Polynomial.ext
  intro b
  by_cases h : a < u ∧ b < J <;>
    simp [Moments.jetScalar, Moments.jetEval_coeff, Squarefree.coeff_canonical, h]

end CanonicalSpecialization

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
