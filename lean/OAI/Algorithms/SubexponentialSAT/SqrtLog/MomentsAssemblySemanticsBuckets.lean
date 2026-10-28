import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemanticsFinite

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable def semanticReadout {n : ℕ} (u J : ℕ) : Jet (Fin n) R →+ Polynomial R :=
  (Truncation.truncAddHom J).comp ((Moments.sumUCoeff u).comp (Moments.jetCoeff ⟨∅⟩))

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (htable : ∀ i j, basis i * basis j =
    ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
  (u J : ℕ)
  (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)

noncomputable def output (entries : List (Product.Entry n (baseWidth p t) d)) : Polynomial R :=
  PolynomialAlgorithm.denote (Moments.outputCoefficients u J
    (Dictionary.denoteTable (coefficient p t M cache scalar basis) entries))

theorem output_eq_semanticReadout (entries : List (Product.Entry n (baseWidth p t) d)) :
    output p t M cache scalar basis u J entries =
      semanticReadout u J (denote p t M cache scalar basis entries) :=
  Moments.outputCoefficients_denote u J _

@[simp] theorem output_nil : output p t M cache scalar basis u J
    ([] : List (Product.Entry n (baseWidth p t) d)) = 0 := by
  rw [output_eq_semanticReadout, denote_nil, map_zero]

/- The concrete outer bucket loop sums the outputs of its actual bucket
contexts. The normalization seed contributes exactly once. -/
include htable in
theorem bucketsRun_output (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d)) (bs : List BucketInput)
    (seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup)
    (ho : denote p t M cache scalar basis one = canonical u J 1) :
    output p t M cache scalar basis u J
      (bucketsRun p t M cache table u J meaning high ss one bs seed) =
      (bs.map fun b => output p t M cache scalar basis u J
        (supportsRun p t M cache table u J meaning (Function.update high 177 b.context)
          b.heads one ss [])).sum + output p t M cache scalar basis u J seed := by
  rw [output_eq_semanticReadout,
    bucketsRun_denote p t M cache scalar basis table htable u J meaning high ss one bs seed hn ho,
    map_add, map_list_sum, output_eq_semanticReadout p t M cache scalar basis u J seed]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  rw [output_eq_semanticReadout,
    supportsRun_denote p t M cache scalar basis table htable u J meaning _ _ one ss []
      (by simp [Sparse.keys]) ho, denote_nil, add_zero]

/- A finite, duplicate-free enumeration of bucket records permits exact
reindexing. Only the already-proved per-bucket answer is a hypothesis. -/
include htable in
theorem bucketsRun_output_finite {Y : Type*} [Fintype Y] [DecidableEq Y]
    (ys : List Y) (hyn : ys.Nodup) (hyc : ys.toFinset = Finset.univ)
    (input : Y → BucketInput) (answer : Y → Polynomial R)
    (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d))
    (ho : denote p t M cache scalar basis one = canonical u J 1)
    (ha : ∀ y, output p t M cache scalar basis u J
      (supportsRun p t M cache table u J meaning
        (Function.update high 177 (input y).context) (input y).heads one ss []) = answer y) :
    output p t M cache scalar basis u J
      (bucketsRun p t M cache table u J meaning high ss one (ys.map input) []) =
        ∑ y, answer y := by
  rw [bucketsRun_output p t M cache scalar basis table htable u J meaning high ss one
    (ys.map input) [] (by simp [Sparse.keys]) ho, output_nil, add_zero]
  simp only [List.map_map, Function.comp_def, ha]
  rw [← List.sum_toFinset answer hyn, hyc]

/- Summing the actual attained signature tuples and their fibers recovers
exactly the original Boolean sum; no rectangular-bucket premise is used. -/
include htable in
theorem bucketsRun_output_boolean {V G : Type*} [Fintype V] [Fintype G]
    [DecidableEq V] [DecidableEq G] {L : G → Type*} [∀ g, DecidableEq (L g)]
    (head : V → G) (label : ∀ g, (Moments.Head head g → Bool) → L g)
    (ys : List (∀ g, Moments.LabelValue label g)) (hyn : ys.Nodup)
    (hyc : ys.toFinset = Finset.univ)
    (input : (∀ g, Moments.LabelValue label g) → BucketInput)
    (answer : (V → Bool) → Polynomial R)
    (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d))
    (ho : denote p t M cache scalar basis one = canonical u J 1)
    (ha : ∀ y, output p t M cache scalar basis u J
      (supportsRun p t M cache table u J meaning
        (Function.update high 177 (input y).context) (input y).heads one ss []) =
      ∑ a : ∀ g, Moments.LabelBucket label g (y g),
        answer (Moments.assemble head (fun g => (a g).val))) :
    output p t M cache scalar basis u J
      (bucketsRun p t M cache table u J meaning high ss one (ys.map input) []) =
        ∑ x : V → Bool, answer x := by
  classical
  rw [bucketsRun_output_finite p t M cache scalar basis table htable u J meaning
    ys hyn hyc input _ high ss one ho ha]
  exact (Moments.sum_boolean_actual_buckets head label answer).symm

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
