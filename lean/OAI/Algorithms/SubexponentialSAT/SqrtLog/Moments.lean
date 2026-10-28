import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSeparation

namespace OAI.Algorithms

/-!
# Squarefree coefficient extraction by independent head moments

The coefficient algebra is an explicit parameter: this file does not identify
ordinary total-degree truncation with Boolean squarefree reduction.  The
squarefree implementation supplies the coefficient add-homs and scalar law.
All sums below are finite, including empty buckets and arbitrary outer labels.
-/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

section Coefficients

variable {A B I G : Type*} [CommSemiring A] [CommSemiring B]
  [Fintype G] [DecidableEq G] {X : G → Type*} [∀ g, Fintype (X g)]

/-- The actual array of weighted local sums for one retained support. -/
def headMoment (scalar : B →+* A) (weight : I → ∀ g, X g → B)
    (localValue : ∀ g, X g → A) (i : I) (g : G) : A :=
  ∑ x : X g, scalar (weight i g x) * localValue g x

/-- Multiply the local sums, retaining their full coefficient algebra. -/
def momentProduct (scalar : B →+* A) (weight : I → ∀ g, X g → B)
    (localValue : ∀ g, X g → A) (i : I) : A :=
  ∏ g, headMoment scalar weight localValue i g

/-- The complete coefficient-extraction algorithm for a finite support list. -/
def extractMoments (supports : Finset I) (scalar : B →+* A)
    (coeff : I → A →+ B) (weight : I → ∀ g, X g → B)
    (localValue : ∀ g, X g → A) : B :=
  ∑ i ∈ supports, coeff i (momentProduct scalar weight localValue i)

/-- Finite distributivity is applied before coefficient extraction. -/
theorem momentProduct_eq_sum (scalar : B →+* A)
    (weight : I → ∀ g, X g → B) (localValue : ∀ g, X g → A) (i : I) :
    momentProduct scalar weight localValue i =
      ∑ x : ∀ g, X g, scalar (∏ g, weight i g (x g)) *
        ∏ g, localValue g (x g) := by
  classical
  unfold momentProduct headMoment
  rw [← SubexponentialSAT.SubexpSeparation.sum_prod_eq_prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_mul_distrib, map_prod]

/-- The single-support moment identity. No field or division is used. -/
theorem coefficient_momentProduct (scalar : B →+* A)
    (coeff : I → A →+ B)
    (hscalar : ∀ i b a, coeff i (scalar b * a) = b * coeff i a)
    (weight : I → ∀ g, X g → B) (localValue : ∀ g, X g → A) (i : I) :
    coeff i (momentProduct scalar weight localValue i) =
      ∑ x : ∀ g, X g, (∏ g, weight i g (x g)) *
        coeff i (∏ g, localValue g (x g)) := by
  rw [momentProduct_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact hscalar i _ _

/-- Sum all retained squarefree coefficients after the head products. -/
theorem extractMoments_eq_sum (supports : Finset I) (scalar : B →+* A)
    (coeff : I → A →+ B)
    (hscalar : ∀ i b a, coeff i (scalar b * a) = b * coeff i a)
    (weight : I → ∀ g, X g → B) (localValue : ∀ g, X g → A) :
    extractMoments supports scalar coeff weight localValue =
      ∑ x : ∀ g, X g, ∑ i ∈ supports,
        (∏ g, weight i g (x g)) * coeff i (∏ g, localValue g (x g)) := by
  classical
  unfold extractMoments
  simp_rw [coefficient_momentProduct scalar coeff hscalar]
  exact Finset.sum_comm

/-- An evaluation expansion is the only bridge needed from the squarefree
algebra. Its support theorem will justify the supplied finite `supports`. -/
theorem extractMoments_eq_evaluated_sum (supports : Finset I)
    (scalar : B →+* A) (coeff : I → A →+ B)
    (hscalar : ∀ i b a, coeff i (scalar b * a) = b * coeff i a)
    (weight : I → ∀ g, X g → B) (localValue : ∀ g, X g → A)
    (evaluate : (∀ g, X g) → A → B)
    (hexpand : ∀ x,
      evaluate x (∏ g, localValue g (x g)) =
        ∑ i ∈ supports, (∏ g, weight i g (x g)) *
          coeff i (∏ g, localValue g (x g))) :
    extractMoments supports scalar coeff weight localValue =
      ∑ x : ∀ g, X g, evaluate x (∏ g, localValue g (x g)) := by
  rw [extractMoments_eq_sum supports scalar coeff hscalar]
  apply Finset.sum_congr rfl
  intro x hx
  exact (hexpand x).symm

end Coefficients

section ActualBuckets

variable {A B I G O Ω : Type*} [CommSemiring A] [CommSemiring B]
  [Fintype G] [DecidableEq G] [Fintype O] [Fintype Ω]
  {X : O → G → Type*} [∀ o g, Fintype (X o g)]

/-- All integer-label tuples are handled separately; their local buckets can
have unequal sizes or be empty. The equivalence is the actual bucket map. -/
theorem extractMoments_actualBuckets (e : Ω ≃ Σ o, ∀ g, X o g)
    (supports : Finset I) (scalar : B →+* A) (coeff : I → A →+ B)
    (hscalar : ∀ i b a, coeff i (scalar b * a) = b * coeff i a)
    (weight : ∀ o, I → ∀ g, X o g → B)
    (localValue : ∀ o g, X o g → A) (target : Ω → B)
    (hexpand : ∀ o x,
      target (e.symm ⟨o, x⟩) =
        ∑ i ∈ supports, (∏ g, weight o i g (x g)) *
          coeff i (∏ g, localValue o g (x g))) :
    (∑ o, extractMoments supports scalar coeff (weight o) (localValue o)) =
      ∑ z : Ω, target z := by
  rw [SubexponentialSAT.SubexpSeparation.sum_reindex_fibers e]
  apply Finset.sum_congr rfl
  intro o ho
  rw [extractMoments_eq_sum supports scalar coeff hscalar]
  apply Finset.sum_congr rfl
  intro x hx
  exact (hexpand o x).symm

end ActualBuckets

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
