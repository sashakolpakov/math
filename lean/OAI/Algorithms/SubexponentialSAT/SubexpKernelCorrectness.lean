import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpMoments
import OAI.Algorithms.SubexponentialSAT.SubexpCounting

namespace OAI.Algorithms

/-!
# Correctness of the executable r-group list kernel

The executable objects are actual lists of raw coefficient expressions.
Enumeration hypotheses assert duplicate-free, complete lists; expression
hypotheses identify each local group program, scalar weight, and outside
weight separately.  No hypothesis supplies a final jet or count.
-/

namespace SubexponentialSAT.SubexpKernelCorrectness

noncomputable section

open scoped BigOperators

theorem list_sum_eq_univ {α M : Type*} [Fintype α] [AddCommMonoid M]
    (xs : List α) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) (f : α → M) :
    (xs.map f).sum = ∑ x, f x := by
  classical
  have hs : xs.toFinset = Finset.univ := by
    ext x
    simp [hc x]
  simpa only [hs] using (List.sum_toFinset f hn).symm

/-- Assemble the actual list of outer blocks and independent inner lists. -/
def buildBlocks {D r : ℕ} {R O : Type*} {X : O → Fin r → Type*}
    (os : List O) (outside : O → SymbolicCost.CoeffList D R)
    (xs : ∀ o g, List (X o g))
    (weights : ∀ o g, X o g → SymbolicCost.CoeffList D R)
    (groups : ∀ o g, X o g → Algorithm.Expr (SymbolicCost.CoeffList D R)) :
    List (SubexpAlgorithm.Block (SymbolicCost.CoeffList D R)) :=
  os.map fun o => SubexpAlgorithm.Block.ofFibers
    (outside o) (xs o) (weights o) (groups o)

theorem rawMomentValue_buildBlocks {D r : ℕ} {R O : Type*}
    {X : O → Fin r → Type*} [CommSemiring R]
    (os : List O) (outside : O → SymbolicCost.CoeffList D R)
    (xs : ∀ o g, List (X o g))
    (weights : ∀ o g, X o g → SymbolicCost.CoeffList D R)
    (groups : ∀ o g, X o g → Algorithm.Expr (SymbolicCost.CoeffList D R)) :
    SubexpAlgorithm.rawMomentValue (buildBlocks os outside xs weights groups) =
      (os.map fun o => SymbolicCost.denote (outside o) * ∏ g,
        ((xs o g).map fun y => SymbolicCost.denote (weights o g y) *
          ((groups o g y).map SymbolicCost.denote).eval).sum).sum := by
  simp [buildBlocks, SubexpAlgorithm.rawMomentValue, SubexpAlgorithm.Block.ofFibers,
    List.map_map, List.map_ofFn, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro o _
  congr 1
  exact Fin.prod_ofFn (fun g =>
    ((xs o g).map fun y => SymbolicCost.denote (weights o g y) *
      ((groups o g y).map SymbolicCost.denote).eval).sum)

/-- Complete enumerations and local expression denotations identify the
kernel's raw polynomial value with the finite separated family sum. -/
theorem rawMomentValue_eq_finiteSum {D r : ℕ} {R O : Type*}
    {X : O → Fin r → Type*} [CommSemiring R] [Fintype O]
    [∀ o g, Fintype (X o g)]
    (os : List O) (hon : os.Nodup) (hoc : ∀ o, o ∈ os)
    (outside : O → SymbolicCost.CoeffList D R)
    (xs : ∀ o g, List (X o g))
    (hxn : ∀ o g, (xs o g).Nodup) (hxc : ∀ o g y, y ∈ xs o g)
    (weights : ∀ o g, X o g → SymbolicCost.CoeffList D R)
    (groups : ∀ o g, X o g → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (C : O → SymbolicCost.Poly D R)
    (W B : ∀ o g, X o g → SymbolicCost.Poly D R)
    (hC : ∀ o, SymbolicCost.denote (outside o) = C o)
    (hW : ∀ o g y, SymbolicCost.denote (weights o g y) = W o g y)
    (hB : ∀ o g y, ((groups o g y).map SymbolicCost.denote).eval = B o g y) :
    SubexpAlgorithm.rawMomentValue (buildBlocks os outside xs weights groups) =
      ∑ o, C o * ∏ g, ∑ y, W o g y * B o g y := by
  rw [rawMomentValue_buildBlocks, list_sum_eq_univ os hon hoc]
  apply Finset.sum_congr rfl
  intro o ho
  rw [hC]
  apply congrArg (C o * ·)
  apply Finset.prod_congr rfl
  intro g hg
  rw [list_sum_eq_univ (xs o g) (hxn o g) (hxc o g)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [hW, hB]

theorem rawMomentValue_eq_familySum {D r : ℕ} {R O Ω : Type*}
    {X : O → Fin r → Type*} [CommSemiring R] [Fintype O] [Fintype Ω]
    [∀ o g, Fintype (X o g)]
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (os : List O) (hon : os.Nodup) (hoc : ∀ o, o ∈ os)
    (outside : O → SymbolicCost.CoeffList D R)
    (xs : ∀ o g, List (X o g))
    (hxn : ∀ o g, (xs o g).Nodup) (hxc : ∀ o g y, y ∈ xs o g)
    (weights : ∀ o g, X o g → SymbolicCost.CoeffList D R)
    (groups : ∀ o g, X o g → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (c : O → R) (wg : ∀ o g, X o g → R)
    (A : Fin r → Ω → SymbolicCost.Poly D R)
    (hC : ∀ o, SymbolicCost.denote (outside o) = WeightedSupport.scalarHom (c o))
    (hW : ∀ o g y, SymbolicCost.denote (weights o g y) =
      WeightedSupport.scalarHom (wg o g y))
    (hB : ∀ o g y, ((groups o g y).map SymbolicCost.denote).eval =
      A g (e.symm ⟨o, Function.update (reps o) g y⟩)) :
    SubexpAlgorithm.rawMomentValue (buildBlocks os outside xs weights groups) =
      SubexpMoments.familySum WeightedSupport.scalarHom e reps A c wg := by
  exact rawMomentValue_eq_finiteSum os hon hoc outside xs hxn hxc weights groups
    (fun o => WeightedSupport.scalarHom (c o))
    (fun o g y => WeightedSupport.scalarHom (wg o g y))
    (fun o g y => A g (e.symm ⟨o, Function.update (reps o) g y⟩)) hC hW hB

/-- The executable weak-composition list gives exactly the retained moment
sum, without enumerating a coordinate box. -/
theorem sum_exponentList_eq_sum_retained {M : Type*} [AddCommMonoid M]
    (D N : ℕ) (f : (Fin D →₀ ℕ) → M) :
    ((Algorithm.exponentList D N).map fun a => f (Finsupp.equivFunOnFinite.symm a)).sum =
      ∑ a ∈ Moments.retained N, f a := by
  classical
  let es := (Algorithm.exponentList D N).map
    (Finsupp.equivFunOnFinite.symm : (Fin D → ℕ) → (Fin D →₀ ℕ))
  have hn : es.Nodup :=
    (Algorithm.exponentList_nodup D N).map Finsupp.equivFunOnFinite.symm.injective
  have hs : es.toFinset = Moments.retained N := by
    ext a
    simp only [List.mem_toFinset, es, List.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      apply (Moments.mem_retained N _).mpr
      simpa [Finsupp.sum_fintype] using (Algorithm.mem_exponentList D N b).mp hb
    · intro ha
      refine ⟨(fun i => a i), ?_, Finsupp.equivFunOnFinite_symm_coe a⟩
      apply (Algorithm.mem_exponentList D N _).mpr
      simpa [Finsupp.sum_fintype] using (Moments.mem_retained N a).mp ha
  simpa only [hs, es, List.map_map, Function.comp_def] using
    (List.sum_toFinset f hn).symm

/-- The concrete jet execution, with its verified weak-composition list,
expressed as a finite sum of canonical polynomial coefficient extractions. -/
theorem executeJet_eq_momentCoefficients {D : ℕ} {R : Type*} [CommSemiring R]
    (blocks : (Fin D → ℕ) →
      List (SubexpAlgorithm.Block (SymbolicCost.CoeffList D R))) :
    SubexpAlgorithm.executeJet blocks = (List.range D).map fun j =>
      (∑ a ∈ Moments.retained (2 * D + 1),
        Algorithm.extractPolynomial a
          (Truncation.canonical (D + 1) D (2 * D + 1)
            (SubexpAlgorithm.rawMomentValue (blocks (fun i => a i))))).coeff j := by
  rw [SubexpAlgorithm.executeJet_eq]
  apply List.map_congr_left
  intro j hj
  rw [Polynomial.finsetSum_coeff]
  exact sum_exponentList_eq_sum_retained D (2 * D + 1)
    (fun a => (Algorithm.extractPolynomial a
      (Truncation.canonical (D + 1) D (2 * D + 1)
        (SubexpAlgorithm.rawMomentValue (blocks (fun i => a i))))).coeff j)

/-- Local full-group expression denotations are sufficient: canonical
projection of the raw executed moment equals the separated symbolic moment.
Independence and factorization are pointwise facts about the input factors. -/
theorem canonical_rawMomentValue_eq_separatedMoment {D r : ℕ} {R O Ω : Type*}
    {X : O → Fin r → Type*} [CommSemiring R] [Fintype O] [Fintype Ω]
    [∀ o g, Fintype (X o g)] (μ : ℕ)
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (os : List O) (hon : os.Nodup) (hoc : ∀ o, o ∈ os)
    (outside : O → SymbolicCost.CoeffList D R)
    (xs : ∀ o g, List (X o g))
    (hxn : ∀ o g, (xs o g).Nodup) (hxc : ∀ o g y, y ∈ xs o g)
    (weights : ∀ o g, X o g → SymbolicCost.CoeffList D R)
    (groups : ∀ o g, X o g → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (P : Fin r → Ω → SymbolicCost.Poly D R)
    (w : Ω → R) (c : O → R) (wg : ∀ o g, X o g → R)
    (hC : ∀ o, SymbolicCost.denote (outside o) = WeightedSupport.scalarHom (c o))
    (hW : ∀ o g y, SymbolicCost.denote (weights o g y) =
      WeightedSupport.scalarHom (wg o g y))
    (hB : ∀ o g y, ((groups o g y).map SymbolicCost.denote).eval =
      P g (e.symm ⟨o, Function.update (reps o) g y⟩))
    (hP : ∀ o g x y, x g = y g →
      P g (e.symm ⟨o, x⟩) = P g (e.symm ⟨o, y⟩))
    (hw : ∀ o x, w (e.symm ⟨o, x⟩) = c o * ∏ g, wg o g (x g)) :
    Truncation.canonical μ D (D + μ)
      (SubexpAlgorithm.rawMomentValue (buildBlocks os outside xs weights groups)) =
        SubexpCounting.separatedMoment μ D e reps P c wg := by
  rw [rawMomentValue_eq_familySum e reps os hon hoc outside xs hxn hxc
    weights groups c wg P hC hW hB]
  rw [SubexpMoments.familySum_eq WeightedSupport.scalarHom e reps P w c wg hP hw]
  rw [Truncation.canonical_sum,
    SubexpCounting.separatedMoment_eq_sum μ D e reps P w c wg hP hw]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Truncation.canonical_scalar_mul, SubexpCounting.groupProduct_eq]

/-- The actual list/dense/postfix jet kernel returns the coefficients of
the symbolic separated jet.  Every program-denotation premise is local to
one outside weight, one inner weight, or one group expression. -/
theorem executeJet_buildBlocks_eq_separatedJet {D r : ℕ} {R O Ω : Type*}
    {X : O → Fin r → Type*} [CommSemiring R] [Fintype O] [Fintype Ω]
    [∀ o g, Fintype (X o g)]
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (os : List O) (hon : os.Nodup) (hoc : ∀ o, o ∈ os)
    (outside : (Fin D → ℕ) → O → SymbolicCost.CoeffList D R)
    (xs : ∀ o g, List (X o g))
    (hxn : ∀ o g, (xs o g).Nodup) (hxc : ∀ o g y, y ∈ xs o g)
    (weights : (Fin D → ℕ) → ∀ o g, X o g → SymbolicCost.CoeffList D R)
    (groups : (Fin D → ℕ) → ∀ o g,
      X o g → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (P : Fin r → Ω → SymbolicCost.Poly D R) (v : Ω → Fin D → R)
    (c : (Fin D →₀ ℕ) → O → R)
    (wg : (Fin D →₀ ℕ) → ∀ o g, X o g → R)
    (hC : ∀ a o, SymbolicCost.denote (outside a o) =
      WeightedSupport.scalarHom (c (Finsupp.equivFunOnFinite.symm a) o))
    (hW : ∀ a o g y, SymbolicCost.denote (weights a o g y) =
      WeightedSupport.scalarHom (wg (Finsupp.equivFunOnFinite.symm a) o g y))
    (hB : ∀ a o g y, ((groups a o g y).map SymbolicCost.denote).eval =
      P g (e.symm ⟨o, Function.update (reps o) g y⟩))
    (hP : ∀ o g x y, x g = y g →
      P g (e.symm ⟨o, x⟩) = P g (e.symm ⟨o, y⟩))
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) =
      c a o * ∏ g, wg a o g (x g)) :
    SubexpAlgorithm.executeJet
      (fun a => buildBlocks os (outside a) xs (weights a) (groups a)) =
      (List.range D).map fun j =>
        (SubexpCounting.separatedJet (D + 1) D e reps P c wg).coeff j := by
  rw [executeJet_eq_momentCoefficients]
  apply List.map_congr_left
  intro j hj
  have hdim : D + (D + 1) = 2 * D + 1 := by omega
  simp only [SubexpCounting.separatedJet, Polynomial.finsetSum_coeff, hdim]
  apply Finset.sum_congr rfl
  intro a ha
  have hcanon := canonical_rawMomentValue_eq_separatedMoment (D + 1) e reps
    os hon hoc (outside (fun i => a i)) xs hxn hxc
    (weights (fun i => a i)) (groups (fun i => a i)) P
    (fun z => Moments.weight a (v z)) (c a) (wg a)
    (fun o => by simpa using hC (fun i => a i) o)
    (fun o g y => by simpa using hW (fun i => a i) o g y)
    (hB (fun i => a i)) hP (hw a)
  have hcanon' : Truncation.canonical (D + 1) D (2 * D + 1)
      (SubexpAlgorithm.rawMomentValue
        (buildBlocks os (outside (fun i => a i)) xs
          (weights (fun i => a i)) (groups (fun i => a i)))) =
      SubexpCounting.separatedMoment (D + 1) D e reps P (c a) (wg a) := by
    simpa only [hdim] using hcanon
  exact congrArg (fun Q => (Algorithm.extractPolynomial a Q).coeff j) hcanon'

/-- Combining the executable bridge with the checked truncation/counting
semantics gives the coefficients of the full truncated input sum.  The
remaining algebraic premises are the local degree filtration and vanishing
of complete high-U coefficients after X substitution. -/
theorem executeJet_buildBlocks_eq_fullSum {D r : ℕ} {R O Ω : Type*}
    {X : O → Fin r → Type*} [CommSemiring R] [Fintype O] [Fintype Ω]
    [∀ o g, Fintype (X o g)]
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (os : List O) (hon : os.Nodup) (hoc : ∀ o, o ∈ os)
    (outside : (Fin D → ℕ) → O → SymbolicCost.CoeffList D R)
    (xs : ∀ o g, List (X o g))
    (hxn : ∀ o g, (xs o g).Nodup) (hxc : ∀ o g y, y ∈ xs o g)
    (weights : (Fin D → ℕ) → ∀ o g, X o g → SymbolicCost.CoeffList D R)
    (groups : (Fin D → ℕ) → ∀ o g,
      X o g → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (P : Fin r → Ω → SymbolicCost.Poly D R) (v : Ω → Fin D → R)
    (c : (Fin D →₀ ℕ) → O → R)
    (wg : (Fin D →₀ ℕ) → ∀ o g, X o g → R)
    (hC : ∀ a o, SymbolicCost.denote (outside a o) =
      WeightedSupport.scalarHom (c (Finsupp.equivFunOnFinite.symm a) o))
    (hW : ∀ a o g y, SymbolicCost.denote (weights a o g y) =
      WeightedSupport.scalarHom (wg (Finsupp.equivFunOnFinite.symm a) o g y))
    (hB : ∀ a o g y, ((groups a o g y).map SymbolicCost.denote).eval =
      P g (e.symm ⟨o, Function.update (reps o) g y⟩))
    (hP : ∀ o g x y, x g = y g →
      P g (e.symm ⟨o, x⟩) = P g (e.symm ⟨o, y⟩))
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) =
      c a o * ∏ g, wg a o g (x g))
    (hdegree : ∀ g z, WeightedSupport.Admissible (P g z))
    (hhigh : ∀ z j, D + 1 ≤ j →
      (Truncation.substX (v z) (∏ g, P g z)).coeff j = 0) :
    SubexpAlgorithm.executeJet
      (fun a => buildBlocks os (outside a) xs (weights a) (groups a)) =
      (List.range D).map fun j =>
        (∑ z, Truncation.trunc D (Truncation.evalXU (v z) (∏ g, P g z))).coeff j := by
  rw [executeJet_buildBlocks_eq_separatedJet e reps os hon hoc outside xs hxn hxc
    weights groups P v c wg hC hW hB hP hw]
  rw [SubexpCounting.separatedJet_eq_sum (D + 1) D e reps P v c wg
    hP hw hdegree hhigh]

end

end SubexponentialSAT.SubexpKernelCorrectness

end OAI.Algorithms
