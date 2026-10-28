import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeJet
import OAI.Algorithms.SubexponentialSAT.Truncation

namespace OAI.Algorithms

/-! Exact coefficient extraction in the Boolean squarefree algebra, including
both formal scalar variables. No total-degree truncation is substituted for
support union. The final U coefficient sum is only an additive operation. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

noncomputable section

section PolynomialScalars

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

theorem mapCoeffs_scalar_mul (scalar : B →+* A) (c : A →+ B)
    (hc : ∀ b a, c (scalar b * a) = b * c a)
    (b : Polynomial B) (a : Polynomial A) :
    Truncation.mapCoeffs c (b.map scalar * a) =
      b * Truncation.mapCoeffs c a := by
  ext j
  simp only [Truncation.coeff_mapCoeffs, Polynomial.coeff_mul, map_sum,
    Polynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro pair hpair
  exact hc _ _

end PolynomialScalars

section SquarefreeEvaluation

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

/-- Retaining a finite superset of the actual support preserves evaluation. -/
theorem squarefree_eval_eq_sum (M : Finset (Support V))
    (f : Poly V R) (x : V → R) (hx : ∀ v, x v * x v = x v)
    (hf : f.coeff.support ⊆ M) :
    evalHom x hx f = ∑ s ∈ M, weight x s.vars * coeff s.vars f := by
  rw [eval_eq_sum]
  change (∑ s ∈ f.coeff.support, f.coeff s * weight x s.vars) = _
  calc
    _ = ∑ s ∈ M, f.coeff s * weight x s.vars := by
      apply Finset.sum_subset hf
      intro s hs hnot
      have hz : f.coeff s = 0 := Finsupp.notMem_support_iff.mp hnot
      simp [hz]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      cases s
      exact mul_comm _ _

/-- U is outermost, Z next, and Boolean squarefree X coefficients innermost. -/
abbrev SquarefreeJet (V R : Type*) [DecidableEq V] [Semiring R] :=
  Polynomial (Polynomial (Poly V R))

abbrev ScalarJet (R : Type*) [Semiring R] := Polynomial (Polynomial R)

def jetScalar : ScalarJet R →+* SquarefreeJet V R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (scalar (V := V) (R := R)))

def jetCoeff (s : Support V) : SquarefreeJet V R →+ ScalarJet R :=
  Truncation.mapCoeffs (Truncation.mapCoeffs (coeffHom s.vars))

@[simp] theorem jetCoeff_apply (s : Support V) (f : SquarefreeJet V R) (u z : ℕ) :
    ((jetCoeff s f).coeff u).coeff z = coeff s.vars ((f.coeff u).coeff z) := rfl

theorem jetCoeff_scalar_mul (s : Support V) (b : ScalarJet R)
    (f : SquarefreeJet V R) :
    jetCoeff s (jetScalar b * f) = b * jetCoeff s f := by
  apply mapCoeffs_scalar_mul
  intro p q
  apply mapCoeffs_scalar_mul
  intro c a
  exact coeff_scalar_mul s.vars c a

def jetEval (x : V → R) (hx : ∀ v, x v * x v = x v) :
    SquarefreeJet V R →+* ScalarJet R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (evalHom x hx))

@[simp] theorem jetEval_coeff (x : V → R) (hx : ∀ v, x v * x v = x v)
    (f : SquarefreeJet V R) (u z : ℕ) :
    ((jetEval x hx f).coeff u).coeff z = evalHom x hx ((f.coeff u).coeff z) := by
  simp [jetEval]

def jetConstant (r : R) : ScalarJet R := Polynomial.C (Polynomial.C r)

theorem jetEval_eq_sum (M : Finset (Support V)) (f : SquarefreeJet V R)
    (x : V → R) (hx : ∀ v, x v * x v = x v)
    (hf : ∀ u z, ((f.coeff u).coeff z).coeff.support ⊆ M) :
    jetEval x hx f = ∑ s ∈ M, jetConstant (weight x s.vars) * jetCoeff s f := by
  ext u z
  simp only [jetEval, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.finsetSum_coeff, jetConstant,
    Polynomial.coeff_C_mul, jetCoeff_apply]
  exact squarefree_eval_eq_sum M ((f.coeff u).coeff z) x hx (hf u z)

/-- Sum the retained U coefficients, after the complete head moment product. -/
def sumUCoeff (t : ℕ) : ScalarJet R →+ Polynomial R where
  toFun f := ∑ u ∈ Finset.range t, f.coeff u
  map_zero' := by simp
  map_add' f g := by simp [Finset.sum_add_distrib]

@[simp] theorem sumUCoeff_coeff (t : ℕ) (f : ScalarJet R) (z : ℕ) :
    (sumUCoeff t f).coeff z = ∑ u ∈ Finset.range t, (f.coeff u).coeff z := by
  simp [sumUCoeff, Polynomial.finsetSum_coeff]

end SquarefreeEvaluation

section SquarefreeHeads

variable {V R G : Type*} [DecidableEq V] [CommSemiring R]
  [Fintype G] [DecidableEq G] {X : G → Type*} [∀ g, Fintype (X g)]

/-- The concrete U/Z/squarefree head identity. `hweight` is supplied by the
actual coordinate partition, and `hbounded` by positive-Z support control. -/
theorem squarefree_head_moments (M : Finset (Support V))
    (D : ∀ g, X g → SquarefreeJet V R) (xval : (∀ g, X g) → V → R)
    (hidem : ∀ x v, xval x v * xval x v = xval x v)
    (w : Support V → ∀ g, X g → ScalarJet R)
    (hweight : ∀ s x,
      jetConstant (weight (xval x) s.vars) = ∏ g, w s g (x g))
    (hbounded : ∀ (x : ∀ g, X g) u z,
      (((∏ g, D g (x g)).coeff u).coeff z).coeff.support ⊆ M) :
    extractMoments M jetScalar jetCoeff w D =
      ∑ x : ∀ g, X g, jetEval (xval x) (hidem x) (∏ g, D g (x g)) := by
  refine extractMoments_eq_evaluated_sum M jetScalar jetCoeff
    (fun s b a => jetCoeff_scalar_mul s b a) w D
    (fun x a => jetEval (xval x) (hidem x) a) ?_
  intro x
  rw [jetEval_eq_sum M _ _ _ (hbounded x)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hweight s x]

theorem squarefree_head_moments_sumU (t : ℕ) (M : Finset (Support V))
    (D : ∀ g, X g → SquarefreeJet V R) (xval : (∀ g, X g) → V → R)
    (hidem : ∀ x v, xval x v * xval x v = xval x v)
    (w : Support V → ∀ g, X g → ScalarJet R)
    (hweight : ∀ s x,
      jetConstant (weight (xval x) s.vars) = ∏ g, w s g (x g))
    (hbounded : ∀ (x : ∀ g, X g) u z,
      (((∏ g, D g (x g)).coeff u).coeff z).coeff.support ⊆ M) :
    sumUCoeff t (extractMoments M jetScalar jetCoeff w D) =
      ∑ x : ∀ g, X g,
        sumUCoeff t (jetEval (xval x) (hidem x) (∏ g, D g (x g))) := by
  rw [squarefree_head_moments M D xval hidem w hweight hbounded, map_sum]

end SquarefreeHeads

section RetainedHeads

variable {V R G : Type*} [DecidableEq V] [CommSemiring R]
  [Fintype G] [DecidableEq G] {X : G → Type*} [∀ g, Fintype (X g)]

/-- Only the coefficient currently being extracted needs its support bound. -/
theorem squarefree_head_moments_coeff (M : Finset (Support V))
    (D : ∀ g, X g → SquarefreeJet V R) (xval : (∀ g, X g) → V → R)
    (hidem : ∀ x v, xval x v * xval x v = xval x v)
    (w : Support V → ∀ g, X g → ScalarJet R)
    (hweight : ∀ s x,
      jetConstant (weight (xval x) s.vars) = ∏ g, w s g (x g))
    (u z : ℕ)
    (hbounded : ∀ (x : ∀ g, X g),
      (((∏ g, D g (x g)).coeff u).coeff z).coeff.support ⊆ M) :
    ((extractMoments M jetScalar jetCoeff w D).coeff u).coeff z =
      ∑ x : ∀ g, X g,
        ((jetEval (xval x) (hidem x) (∏ g, D g (x g))).coeff u).coeff z := by
  rw [extractMoments_eq_sum M jetScalar jetCoeff (fun s b a => jetCoeff_scalar_mul s b a)]
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [← hweight]
  simp only [jetConstant, Polynomial.coeff_C_mul, jetCoeff_apply, jetEval_coeff]
  exact (squarefree_eval_eq_sum M _ _ _ (hbounded x)).symm

/-- The actual retained U/Z computation only enumerates supports of size <J.
Admissibility of the untruncated factors proves this bound at every stage. -/
theorem squarefree_head_moments_trunc (t J : ℕ) (M : Finset (Support V))
    (hM : ∀ s : Support V, s.vars.card < J → s ∈ M)
    (D : ∀ g, X g → SquarefreeJet V R)
    (hD : ∀ g y, Squarefree.Admissible (D g y))
    (xval : (∀ g, X g) → V → R)
    (hidem : ∀ x v, xval x v * xval x v = xval x v)
    (w : Support V → ∀ g, X g → ScalarJet R)
    (hweight : ∀ s x,
      jetConstant (weight (xval x) s.vars) = ∏ g, w s g (x g)) :
    Truncation.trunc J (sumUCoeff t (extractMoments M jetScalar jetCoeff w D)) =
      ∑ x : ∀ g, X g,
        Truncation.trunc J (sumUCoeff t
          (jetEval (xval x) (hidem x) (∏ g, D g (x g)))) := by
  classical
  ext z
  by_cases hz : z < J
  · simp only [Truncation.coeff_trunc, hz, ite_true, sumUCoeff_coeff,
      Polynomial.finsetSum_coeff]
    -- Rewrite each retained coefficient before changing the order of sums.
    have hc : ∀ u,
        ((extractMoments M jetScalar jetCoeff w D).coeff u).coeff z =
          ∑ x : ∀ g, X g,
            ((jetEval (xval x) (hidem x) (∏ g, D g (x g))).coeff u).coeff z := by
      intro u
      apply squarefree_head_moments_coeff M D xval hidem w hweight u z
      intro y s hs
      have hadm : Squarefree.Admissible (∏ g, D g (y g)) :=
        Squarefree.admissible_prod Finset.univ (fun g => D g (y g))
          (fun g _ => hD g (y g))
      exact hM s ((hadm u z s hs).trans_lt hz)
    simp_rw [hc]
    exact Finset.sum_comm
  · simp [Truncation.coeff_trunc, hz, Polynomial.finsetSum_coeff]

end RetainedHeads

end
end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
