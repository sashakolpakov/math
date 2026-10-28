import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.QuarticSearch

namespace OAI.Algorithms

/-!
# Explicit exhaustive linear-algebra search on a finite universal block

The execution functions use lists of field elements and explicitly enumerate
vectors and scalar coefficient tuples. No decision procedure for the proposition
`LinearIndependent` or for an abstract span is executed.
-/

namespace SubexponentialSAT.Subexp.BlockSearch

open scoped BigOperators
open SubexponentialSAT.QuarticSearch

variable {K : Type*} [Field K] [DecidableEq K]

abbrev Vec (K : Type*) (N : ℕ) := Fin N → K

/-- A tuple of at most `N` explicitly represented vectors. -/
abbrev Candidate (K : Type*) (N : ℕ) :=
  Σ d : Fin (N + 1), Fin d.val → Vec K N

def combine {N : ℕ} (c : Candidate K N) (a : Fin c.1.val → K) : Vec K N :=
  ∑ i, a i • c.2 i

def matrixMap {m N : ℕ} (M : Fin m → Fin N → K) :
    Vec K N →ₗ[K] Vec K m where
  toFun x i := ∑ j, M i j * x j
  map_add' x y := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by ext i; simp [Finset.mul_sum, mul_left_comm ]

/-- Enumerate dimensions, then all vector tuples of that dimension. -/
def candidates (alphabet : List K) (N : ℕ) : List (Candidate K N) :=
  (List.finRange (N + 1)).flatMap fun d =>
    (vectors (vectors alphabet N) d.val).map fun v => ⟨d, v⟩

omit [Field K] [DecidableEq K] in
theorem mem_candidates (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {N : ℕ} (c : Candidate K N) : c ∈ candidates alphabet N := by
  apply List.mem_flatMap.mpr
  refine ⟨c.1, by simp, ?_⟩
  apply List.mem_map.mpr
  refine ⟨c.2, ?_, rfl⟩
  exact mem_vectors _ (fun v => mem_vectors alphabet hc N v) _ c.2

omit [Field K] [DecidableEq K] in
theorem all_vectors_iff (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    (d : ℕ) (test : (Fin d → K) → Bool) :
    (vectors alphabet d).all test = true ↔ ∀ v, test v = true := by
  simp only [List.all_eq_true]
  constructor
  · intro h v
    exact h v (mem_vectors alphabet hc d v)
  · intro h v _
    exact h v

omit [Field K] [DecidableEq K] in
theorem any_vectors_iff (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    (d : ℕ) (test : (Fin d → K) → Bool) :
    (vectors alphabet d).any test = true ↔ ∃ v, test v = true := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨v, _, hv⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, mem_vectors alphabet hc d v, hv⟩

/-- All independence, membership, and spanning checks are finite loops. -/
def basisTest (alphabet : List K) {m N : ℕ} (M : Fin m → Fin N → K)
    (c : Candidate K N) : Bool :=
  (vectors alphabet c.1.val).all (fun a =>
    if combine c a = 0 then decide (a = 0) else true) &&
  (List.finRange c.1.val).all (fun i => decide (matrixMap M (c.2 i) = 0)) &&
  (vectors alphabet N).all (fun x =>
    if matrixMap M x = 0 then
      (vectors alphabet c.1.val).any (fun a => decide (combine c a = x))
    else true)

def GoodBasis {m N : ℕ} (M : Fin m → Fin N → K) (c : Candidate K N) : Prop :=
  (∀ a, combine c a = 0 → a = 0) ∧
  (∀ i, matrixMap M (c.2 i) = 0) ∧
  (∀ x, matrixMap M x = 0 → ∃ a, combine c a = x)

theorem basisTest_iff (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) (c : Candidate K N) :
    basisTest alphabet M c = true ↔ GoodBasis M c := by
  simp [basisTest, GoodBasis, all_vectors_iff alphabet hc,
    any_vectors_iff alphabet hc, Bool.and_eq_true, and_assoc, ← imp_iff_not_or]

omit [DecidableEq K] in
theorem GoodBasis.linearIndependent {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N} (h : GoodBasis M c) : LinearIndependent K c.2 := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  exact congrFun (h.1 a ha) i

omit [DecidableEq K] in
theorem GoodBasis.mem_kernel_iff {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N} (h : GoodBasis M c) (x : Vec K N) :
    x ∈ LinearMap.ker (matrixMap M) ↔ ∃ a, combine c a = x := by
  constructor
  · exact h.2.2 x
  · rintro ⟨a, rfl⟩
    simp only [LinearMap.mem_ker, combine, map_sum, map_smul, h.2.1,
      smul_zero, Finset.sum_const_zero]

/-- This witness is used only to prove that the executable enumeration succeeds. -/
noncomputable def subspaceCandidate {N : ℕ} (P : Submodule K (Vec K N)) :
    Candidate K N :=
  ⟨⟨Module.finrank K P, by
    have h := P.finrank_le
    rw [Module.finrank_pi, Fintype.card_fin] at h
    exact Nat.lt_succ_of_le h⟩,
   fun i => (Module.finBasis K P i : Vec K N)⟩

omit [DecidableEq K] in
theorem combine_subspaceCandidate {N : ℕ} (P : Submodule K (Vec K N))
    (a : Fin (Module.finrank K P) → K) :
    combine (subspaceCandidate P) a =
      ((Module.finBasis K P).equivFun.symm a : Vec K N) := by
  change (∑ i, a i • P.subtype (Module.finBasis K P i)) =
    P.subtype ((Module.finBasis K P).equivFun.symm a)
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul]

omit [DecidableEq K] in
theorem subspaceCandidate_independent {N : ℕ} (P : Submodule K (Vec K N))
    (a : Fin (Module.finrank K P) → K)
    (ha : combine (subspaceCandidate P) a = 0) : a = 0 := by
  rw [combine_subspaceCandidate] at ha
  have hz : (Module.finBasis K P).equivFun.symm a = 0 := Subtype.ext ha
  apply (Module.finBasis K P).equivFun.symm.injective
  simpa only [map_zero] using hz

omit [DecidableEq K] in
theorem subspaceCandidate_spans {N : ℕ} (P : Submodule K (Vec K N)) (x : P) :
    ∃ a, combine (subspaceCandidate P) a = (x : Vec K N) := by
  refine ⟨(Module.finBasis K P).equivFun x, ?_⟩
  rw [combine_subspaceCandidate, LinearEquiv.symm_apply_apply]

omit [DecidableEq K] in
theorem exists_goodBasis {m N : ℕ} (M : Fin m → Fin N → K) :
    ∃ c : Candidate K N, GoodBasis M c := by
  let P := LinearMap.ker (matrixMap M)
  refine ⟨subspaceCandidate P, ?_, ?_, ?_⟩
  · exact subspaceCandidate_independent P
  · intro i
    exact (Module.finBasis K P i).2
  · intro x hx
    exact subspaceCandidate_spans P ⟨x, hx⟩

/-- Executable search; no abstract linear-algebra predicate occurs in its code. -/
def searchBasis (alphabet : List K) {m N : ℕ} (M : Fin m → Fin N → K) :
    Option (Candidate K N) :=
  (candidates alphabet N).find? (basisTest alphabet M)

theorem searchBasis_sound (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} {M : Fin m → Fin N → K} {c : Candidate K N}
    (h : searchBasis alphabet M = some c) : GoodBasis M c :=
  (basisTest_iff alphabet hc M c).mp (List.find?_some h)

theorem searchBasis_isSome (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) : (searchBasis alphabet M).isSome := by
  apply List.find?_isSome.mpr
  obtain ⟨c, hc'⟩ := exists_goodBasis M
  exact ⟨c, mem_candidates alphabet hc c, (basisTest_iff alphabet hc M c).mpr hc'⟩

/-- A total executable basis finder. The existence proof is erased by execution. -/
def findBasis (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) : Candidate K N :=
  (searchBasis alphabet M).get (searchBasis_isSome alphabet hc M)

theorem findBasis_good (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) : GoodBasis M (findBasis alphabet hc M) := by
  apply searchBasis_sound alphabet hc
  exact (Option.some_get _).symm

/-- A kernel basis together with a complementary basis, certified by scalar tests. -/
def GoodPair {m N : ℕ} (M : Fin m → Fin N → K)
    (c : Candidate K N × Candidate K N) : Prop :=
  GoodBasis M c.1 ∧
  (∀ a b, combine c.1 a + combine c.2 b = 0 → a = 0 ∧ b = 0) ∧
  (∀ x : Vec K N, ∃ a b, combine c.1 a + combine c.2 b = x)

def pairTest (alphabet : List K) {m N : ℕ} (M : Fin m → Fin N → K)
    (c : Candidate K N × Candidate K N) : Bool :=
  basisTest alphabet M c.1 &&
  (vectors alphabet c.1.1.val).all (fun a =>
    (vectors alphabet c.2.1.val).all (fun b =>
      if combine c.1 a + combine c.2 b = 0 then decide (a = 0 ∧ b = 0) else true)) &&
  (vectors alphabet N).all (fun x =>
    (vectors alphabet c.1.1.val).any (fun a =>
      (vectors alphabet c.2.1.val).any (fun b =>
        decide (combine c.1 a + combine c.2 b = x))))

theorem pairTest_iff (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) (c : Candidate K N × Candidate K N) :
    pairTest alphabet M c = true ↔ GoodPair M c := by
  simp [pairTest, GoodPair, basisTest_iff alphabet hc, all_vectors_iff alphabet hc,
    any_vectors_iff alphabet hc, Bool.and_eq_true, and_assoc, ← imp_iff_not_or]

omit [DecidableEq K] in
theorem exists_goodPair {m N : ℕ} (M : Fin m → Fin N → K) :
    ∃ c : Candidate K N × Candidate K N, GoodPair M c := by
  classical
  let P := LinearMap.ker (matrixMap M)
  obtain ⟨Q, hPQ⟩ := P.exists_isCompl
  let E := Submodule.prodEquivOfIsCompl P Q hPQ
  refine ⟨(subspaceCandidate P, subspaceCandidate Q), ?_, ?_, ?_⟩
  · exact ⟨subspaceCandidate_independent P,
      fun i => (Module.finBasis K P i).2,
      fun x hx => subspaceCandidate_spans P ⟨x, hx⟩⟩
  · intro a b hab
    change combine (subspaceCandidate P) a + combine (subspaceCandidate Q) b = 0 at hab
    have hab' : ((Module.finBasis K P).equivFun.symm a : Vec K N) +
        ((Module.finBasis K Q).equivFun.symm b : Vec K N) = 0 := by
      calc
        _ = combine (subspaceCandidate P) a + combine (subspaceCandidate Q) b :=
          congrArg₂ (· + ·) (combine_subspaceCandidate P a).symm
            (combine_subspaceCandidate Q b).symm
        _ = 0 := hab
    have hz : E ((Module.finBasis K P).equivFun.symm a,
        (Module.finBasis K Q).equivFun.symm b) = E 0 := by
      simpa only [E, Submodule.coe_prodEquivOfIsCompl', Prod.fst_zero, Prod.snd_zero,
        Submodule.coe_zero, add_zero] using hab'
    have hz' := E.injective hz
    constructor
    · apply (Module.finBasis K P).equivFun.symm.injective
      calc
        _ = 0 := by simpa only [Prod.fst_zero] using congrArg Prod.fst hz'
        _ = (Module.finBasis K P).equivFun.symm 0 := (map_zero _).symm
    · apply (Module.finBasis K Q).equivFun.symm.injective
      calc
        _ = 0 := by simpa only [Prod.snd_zero] using congrArg Prod.snd hz'
        _ = (Module.finBasis K Q).equivFun.symm 0 := (map_zero _).symm
  · intro x
    refine ⟨(Module.finBasis K P).equivFun (E.symm x).1,
      (Module.finBasis K Q).equivFun (E.symm x).2, ?_⟩
    rw [combine_subspaceCandidate, combine_subspaceCandidate]
    simp only [LinearEquiv.symm_apply_apply]
    exact E.apply_symm_apply x

/-- Search pairs of bounded-length tuples, still only on the universal block. -/
def searchPair (alphabet : List K) {m N : ℕ} (M : Fin m → Fin N → K) :
    Option (Candidate K N × Candidate K N) :=
  ((candidates alphabet N).product (candidates alphabet N)).find? (pairTest alphabet M)

theorem searchPair_sound (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} {M : Fin m → Fin N → K} {c : Candidate K N × Candidate K N}
    (h : searchPair alphabet M = some c) : GoodPair M c :=
  (pairTest_iff alphabet hc M c).mp (List.find?_some h)

theorem searchPair_isSome (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) : (searchPair alphabet M).isSome := by
  apply List.find?_isSome.mpr
  obtain ⟨c, hc'⟩ := exists_goodPair M
  refine ⟨c, ?_, (pairTest_iff alphabet hc M c).mpr hc'⟩
  exact List.mem_product.mpr ⟨mem_candidates alphabet hc c.1,
    mem_candidates alphabet hc c.2⟩

def findPair (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) : Candidate K N × Candidate K N :=
  (searchPair alphabet M).get (searchPair_isSome alphabet hc M)

theorem findPair_good (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) : GoodPair M (findPair alphabet hc M) := by
  apply searchPair_sound alphabet hc
  exact (Option.some_get _).symm

omit [DecidableEq K] in
@[simp] theorem combine_zero {N : ℕ} (c : Candidate K N) : combine c 0 = 0 := by
  simp [combine]

omit [DecidableEq K] in
@[simp] theorem combine_neg {N : ℕ} (c : Candidate K N) (a : Fin c.1.val → K) :
    combine c (-a) = -combine c a := by simp [combine, Finset.sum_neg_distrib]

omit [DecidableEq K] in
theorem combine_sub {N : ℕ} (c : Candidate K N) (a b : Fin c.1.val → K) :
    combine c (a - b) = combine c a - combine c b := by
  simp [combine, sub_smul, Finset.sum_sub_distrib]

def combineLinear {N : ℕ} (c : Candidate K N) :
    (Fin c.1.val → K) →ₗ[K] Vec K N where
  toFun := combine c
  map_add' a b := by simp [combine, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [combine, smul_smul, Finset.smul_sum]

omit [DecidableEq K] in
theorem finrank_range_combine {N : ℕ} (c : Candidate K N)
    (h : ∀ a, combine c a = 0 → a = 0) :
    Module.finrank K (LinearMap.range (combineLinear c)) = c.1.val := by
  have hi : Function.Injective (combineLinear c) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply h
    rw [combine_sub]
    exact sub_eq_zero.mpr hab
  calc
    _ = Module.finrank K (Fin c.1.val → K) :=
      (LinearEquiv.ofInjective (combineLinear c) hi).finrank_eq.symm
    _ = _ := by rw [Module.finrank_pi, Fintype.card_fin]

omit [DecidableEq K] in
theorem GoodBasis.finrank_kernel {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N} (h : GoodBasis M c) :
    Module.finrank K (LinearMap.ker (matrixMap M)) = c.1.val := by
  have he : LinearMap.ker (matrixMap M) = LinearMap.range (combineLinear c) := by
    ext x
    exact h.mem_kernel_iff x
  rw [he]
  exact finrank_range_combine c h.1

omit [DecidableEq K] in
theorem GoodPair.existsUnique_decomposition {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (h : GoodPair M c) (x : Vec K N) :
    ∃! ab : (Fin c.1.1.val → K) × (Fin c.2.1.val → K),
      combine c.1 ab.1 + combine c.2 ab.2 = x := by
  obtain ⟨a, b, hab⟩ := h.2.2 x
  refine ⟨(a, b), hab, ?_⟩
  rintro ⟨a', b'⟩ hab'
  have hz : combine c.1 (a' - a) + combine c.2 (b' - b) = 0 := by
    rw [combine_sub, combine_sub]
    calc
      _ = (combine c.1 a' + combine c.2 b') -
          (combine c.1 a + combine c.2 b) := by abel
      _ = 0 := by rw [hab', hab, sub_self]
  obtain ⟨ha, hb⟩ := h.2.1 _ _ hz
  exact Prod.ext (sub_eq_zero.mp ha) (sub_eq_zero.mp hb)

omit [DecidableEq K] in
theorem GoodPair.complement_independent {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (h : GoodPair M c) :
    LinearIndependent K c.2.2 := by
  apply Fintype.linearIndependent_iff.mpr
  intro b hb i
  change combine c.2 b = 0 at hb
  have hz := (h.2.1 0 b (by rw [combine_zero, zero_add]; exact hb)).2
  exact congrFun hz i

omit [DecidableEq K] in
theorem GoodPair.finrank_complement {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (h : GoodPair M c) :
    Module.finrank K (LinearMap.range (combineLinear c.2)) = c.2.1.val := by
  apply finrank_range_combine
  intro b hb
  exact (h.2.1 0 b (by simpa only [combine_zero, zero_add] using hb)).2

omit [DecidableEq K] in
theorem GoodPair.isCompl {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (h : GoodPair M c) :
    IsCompl (LinearMap.ker (matrixMap M)) (LinearMap.range (combineLinear c.2)) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hy
    obtain ⟨a, ha⟩ := (h.1.mem_kernel_iff x).mp hx
    obtain ⟨b, hb⟩ := hy
    have hz : combine c.1 a + combine c.2 (-b) = 0 := by
      change combine c.2 b = x at hb
      rw [combine_neg, ha, hb, add_neg_cancel]
    have ha0 := (h.2.1 a (-b) hz).1
    rw [← ha, ha0, combine_zero]
  · apply codisjoint_iff_le_sup.mpr
    intro x _
    obtain ⟨a, b, hab⟩ := h.2.2 x
    apply Submodule.mem_sup.mpr
    exact ⟨combine c.1 a, (h.1.mem_kernel_iff _).mpr ⟨a, rfl⟩,
      combine c.2 b, ⟨b, rfl⟩, hab⟩

def coefficientPairs (alphabet : List K) {N : ℕ}
    (c : Candidate K N × Candidate K N) :
    List ((Fin c.1.1.val → K) × (Fin c.2.1.val → K)) :=
  (vectors alphabet c.1.1.val).product (vectors alphabet c.2.1.val)

def searchCoordinates (alphabet : List K) {N : ℕ}
    (c : Candidate K N × Candidate K N) (x : Vec K N) :=
  (coefficientPairs alphabet c).find? fun ab =>
    decide (combine c.1 ab.1 + combine c.2 ab.2 = x)

theorem searchCoordinates_isSome (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} {M : Fin m → Fin N → K} (c : Candidate K N × Candidate K N)
    (hg : GoodPair M c) (x : Vec K N) : (searchCoordinates alphabet c x).isSome := by
  apply List.find?_isSome.mpr
  obtain ⟨a, b, hab⟩ := hg.2.2 x
  refine ⟨(a, b), ?_, by simpa using hab⟩
  exact List.mem_product.mpr ⟨mem_vectors alphabet hc _ a, mem_vectors alphabet hc _ b⟩

/-- The inverse coordinate map is a finite local search, not a chosen existential witness. -/
def decomposePair (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} {M : Fin m → Fin N → K} (c : Candidate K N × Candidate K N)
    (hg : GoodPair M c) (x : Vec K N) :
    (Fin c.1.1.val → K) × (Fin c.2.1.val → K) :=
  (searchCoordinates alphabet c x).get (searchCoordinates_isSome alphabet hc c hg x)

theorem decomposePair_spec (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} {M : Fin m → Fin N → K} (c : Candidate K N × Candidate K N)
    (hg : GoodPair M c) (x : Vec K N) :
    combine c.1 (decomposePair alphabet hc c hg x).1 +
      combine c.2 (decomposePair alphabet hc c hg x).2 = x := by
  have h := List.find?_some (show searchCoordinates alphabet c x =
    some (decomposePair alphabet hc c hg x) from (Option.some_get _).symm)
  simpa using h

/-- An executable local coordinate equivalence, with a direct linear-combination inverse. -/
def pairEquiv (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} {M : Fin m → Fin N → K} (c : Candidate K N × Candidate K N)
    (hg : GoodPair M c) : Vec K N ≃
    ((Fin c.1.1.val → K) × (Fin c.2.1.val → K)) where
  toFun := decomposePair alphabet hc c hg
  invFun ab := combine c.1 ab.1 + combine c.2 ab.2
  left_inv := decomposePair_spec alphabet hc c hg
  right_inv ab := by
    obtain ⟨z, hz, hu⟩ := hg.existsUnique_decomposition
      (combine c.1 ab.1 + combine c.2 ab.2)
    exact (hu _ (decomposePair_spec alphabet hc c hg _)).trans (hu ab rfl).symm

theorem pairEquiv_apply_kernel (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} {M : Fin m → Fin N → K} (c : Candidate K N × Candidate K N)
    (hg : GoodPair M c) (a : Fin c.1.1.val → K) :
    pairEquiv alphabet hc c hg (combine c.1 a) = (a, 0) := by
  have h := (pairEquiv alphabet hc c hg).apply_symm_apply (a, 0)
  change pairEquiv alphabet hc c hg (combine c.1 a + combine c.2 0) = (a, 0) at h
  simpa only [combine_zero, add_zero] using h

/-- Kernel coordinates, obtained from the executable local decomposition search. -/
def kernelCoeffsEquiv (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} {M : Fin m → Fin N → K} (c : Candidate K N × Candidate K N)
    (hg : GoodPair M c) : (Fin c.1.1.val → K) ≃ LinearMap.ker (matrixMap M) where
  toFun a := ⟨combine c.1 a, (hg.1.mem_kernel_iff _).mpr ⟨a, rfl⟩⟩
  invFun x := (pairEquiv alphabet hc c hg x.1).1
  left_inv a := congrArg Prod.fst (pairEquiv_apply_kernel alphabet hc c hg a)
  right_inv x := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := (hg.1.mem_kernel_iff x.1).mp x.2
    change combine c.1 (pairEquiv alphabet hc c hg x.1).1 = x.1
    rw [← ha, pairEquiv_apply_kernel]

omit [Field K] [DecidableEq K] in
theorem coefficientPairs_length (alphabet : List K) {N : ℕ}
    (c : Candidate K N × Candidate K N) :
    (coefficientPairs alphabet c).length = alphabet.length ^ (c.1.1.val + c.2.1.val) := by
  change List.length (vectors alphabet c.1.1.val ×ˢ vectors alphabet c.2.1.val) = _
  rw [List.length_product, length_vectors, length_vectors, pow_add]

/-- A general finite-list enumeration bound, independent of any mathematical oracle. -/
private theorem length_flatMap_le {A B : Type*} (xs : List A) (f : A → List B) (b : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ b) : (xs.flatMap f).length ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
      have hx := h x (by simp)
      have hxs := ih (fun y hy => h y (by simp [hy]))
      omega

omit [Field K] [DecidableEq K] in
theorem candidates_length_le (alphabet : List K) (hq : 0 < alphabet.length) (N : ℕ) :
    (candidates alphabet N).length ≤ (N + 1) * alphabet.length ^ (N * N) := by
  unfold candidates
  have h := length_flatMap_le (List.finRange (N + 1))
    (fun d => (vectors (vectors alphabet N) d.val).map (fun v => (⟨d, v⟩ : Candidate K N)))
    (alphabet.length ^ (N * N)) (by
      intro d _
      simp only [List.length_map, length_vectors, ← pow_mul]
      exact Nat.pow_le_pow_right hq (Nat.mul_le_mul_left N (Nat.le_of_lt_succ d.2)))
  simpa using h

omit [Field K] [DecidableEq K] in
theorem pair_candidates_length_le (alphabet : List K) (hq : 0 < alphabet.length) (N : ℕ) :
    ((candidates alphabet N).product (candidates alphabet N)).length ≤
      (N + 1)^2 * alphabet.length ^ (2 * N * N) := by
  change List.length (candidates alphabet N ×ˢ candidates alphabet N) ≤ _
  rw [List.length_product]
  calc
    _ ≤ ((N + 1) * alphabet.length ^ (N * N)) *
        ((N + 1) * alphabet.length ^ (N * N)) :=
      Nat.mul_le_mul (candidates_length_le alphabet hq N)
        (candidates_length_le alphabet hq N)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_two, ← pow_add]
      have he : N * N + N * N = 2 * N * N := by ring
      rw [he]

omit [DecidableEq K] in
theorem alphabet_length_pos (alphabet : List K) (hc : ∀ a, a ∈ alphabet) :
    0 < alphabet.length := List.length_pos_iff.mpr (by
      intro h
      have := hc 0
      simp [h] at this)

/-- Instrumented full traversal: the second component counts scheduled primitive checks. -/
def checkedAll {A : Type*} : List A → (A → Bool × ℕ) → Bool × ℕ
  | [], _ => (true, 0)
  | x :: xs, f =>
      let a := f x
      let b := checkedAll xs f
      (a.1 && b.1, a.2 + b.2)

def checkedAny {A : Type*} : List A → (A → Bool × ℕ) → Bool × ℕ
  | [], _ => (false, 0)
  | x :: xs, f =>
      let a := f x
      let b := checkedAny xs f
      (a.1 || b.1, a.2 + b.2)

@[simp] theorem checkedAll_fst {A : Type*} (xs : List A) (f : A → Bool × ℕ) :
    (checkedAll xs f).1 = xs.all (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [checkedAll, ih]

@[simp] theorem checkedAny_fst {A : Type*} (xs : List A) (f : A → Bool × ℕ) :
    (checkedAny xs f).1 = xs.any (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [checkedAny, ih]

@[simp] theorem checkedAll_snd {A : Type*} (xs : List A) (f : A → Bool × ℕ) :
    (checkedAll xs f).2 = (xs.map (fun x => (f x).2)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [checkedAll, ih]

@[simp] theorem checkedAny_snd {A : Type*} (xs : List A) (f : A → Bool × ℕ) :
    (checkedAny xs f).2 = (xs.map (fun x => (f x).2)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [checkedAny, ih]

def checkedBasisTest (alphabet : List K) {m N : ℕ} (M : Fin m → Fin N → K)
    (c : Candidate K N) : Bool × ℕ :=
  let a := checkedAll (vectors alphabet c.1.val) fun a =>
    (if combine c a = 0 then decide (a = 0) else true, 2)
  let b := checkedAll (List.finRange c.1.val) fun i =>
    (decide (matrixMap M (c.2 i) = 0), 1)
  let d := checkedAll (vectors alphabet N) fun x =>
    let r := checkedAny (vectors alphabet c.1.val) fun a =>
      (decide (combine c a = x), 1)
    (if matrixMap M x = 0 then r.1 else true, 1 + r.2)
  (a.1 && b.1 && d.1, a.2 + b.2 + d.2)

@[simp] theorem checkedBasisTest_fst (alphabet : List K) {m N : ℕ}
    (M : Fin m → Fin N → K) (c : Candidate K N) :
    (checkedBasisTest alphabet M c).1 = basisTest alphabet M c := by
  simp [checkedBasisTest, basisTest]

theorem checkedBasisTest_count (alphabet : List K) {m N : ℕ}
    (M : Fin m → Fin N → K) (c : Candidate K N) :
    (checkedBasisTest alphabet M c).2 =
      2 * alphabet.length ^ c.1.val + c.1.val +
        alphabet.length ^ N * (1 + alphabet.length ^ c.1.val) := by
  simp [checkedBasisTest, length_vectors, Nat.mul_comm]

def checkedPairTest (alphabet : List K) {m N : ℕ} (M : Fin m → Fin N → K)
    (c : Candidate K N × Candidate K N) : Bool × ℕ :=
  let base := checkedBasisTest alphabet M c.1
  let ind := checkedAll (vectors alphabet c.1.1.val) fun a =>
    checkedAll (vectors alphabet c.2.1.val) fun b =>
      (if combine c.1 a + combine c.2 b = 0 then decide (a = 0 ∧ b = 0) else true, 3)
  let span := checkedAll (vectors alphabet N) fun x =>
    checkedAny (vectors alphabet c.1.1.val) fun a =>
      checkedAny (vectors alphabet c.2.1.val) fun b =>
        (decide (combine c.1 a + combine c.2 b = x), 1)
  (base.1 && ind.1 && span.1, base.2 + ind.2 + span.2)

@[simp] theorem checkedPairTest_fst (alphabet : List K) {m N : ℕ}
    (M : Fin m → Fin N → K) (c : Candidate K N × Candidate K N) :
    (checkedPairTest alphabet M c).1 = pairTest alphabet M c := by
  simp [checkedPairTest, pairTest]

theorem checkedPairTest_count (alphabet : List K) {m N : ℕ}
    (M : Fin m → Fin N → K) (c : Candidate K N × Candidate K N) :
    (checkedPairTest alphabet M c).2 =
      2 * alphabet.length ^ c.1.1.val + c.1.1.val +
        alphabet.length ^ N * (1 + alphabet.length ^ c.1.1.val) +
        alphabet.length ^ c.1.1.val * (alphabet.length ^ c.2.1.val * 3) +
        alphabet.length ^ N * (alphabet.length ^ c.1.1.val * alphabet.length ^ c.2.1.val) := by
  simp [checkedPairTest, checkedBasisTest_count, length_vectors, Nat.mul_comm ]

theorem checkedPairTest_count_le (alphabet : List K) (hq : 0 < alphabet.length)
    {m N : ℕ} (M : Fin m → Fin N → K) (c : Candidate K N × Candidate K N) :
    (checkedPairTest alphabet M c).2 ≤ (N + 10) * (alphabet.length ^ N + 1)^3 := by
  rw [checkedPairTest_count]
  have hd : c.1.1.val ≤ N := Nat.le_of_lt_succ c.1.1.2
  have he : c.2.1.val ≤ N := Nat.le_of_lt_succ c.2.1.2
  have hdp := Nat.pow_le_pow_right hq hd
  have hep := Nat.pow_le_pow_right hq he
  calc
    _ ≤ 2 * alphabet.length ^ N + N +
        alphabet.length ^ N * (1 + alphabet.length ^ N) +
        alphabet.length ^ N * (alphabet.length ^ N * 3) +
        alphabet.length ^ N * (alphabet.length ^ N * alphabet.length ^ N) := by
      gcongr
    _ ≤ _ := by
      generalize alphabet.length ^ N = p
      ring_nf
      omega

/-- Instrumented search counts the checks performed up to the first successful candidate. -/
def checkedFind {A : Type*} : List A → (A → Bool × ℕ) → Option A × ℕ
  | [], _ => (none, 0)
  | x :: xs, f =>
      let a := f x
      if a.1 then (some x, a.2) else
        let b := checkedFind xs f
        (b.1, a.2 + b.2)

@[simp] theorem checkedFind_fst {A : Type*} (xs : List A) (f : A → Bool × ℕ) :
    (checkedFind xs f).1 = xs.find? (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hfx : (f x).1 <;> simp [checkedFind, List.find?, ih, hfx]

theorem checkedFind_count_le {A : Type*} (xs : List A) (f : A → Bool × ℕ) (b : ℕ)
    (h : ∀ x ∈ xs, (f x).2 ≤ b) : (checkedFind xs f).2 ≤ xs.length * b := by
  induction xs with
  | nil => simp [checkedFind]
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs := ih (fun y hy => h y (by simp [hy]))
      simp only [checkedFind, List.length_cons, Nat.add_mul, Nat.one_mul]
      split_ifs <;> simp only <;> omega

def checkedSearchPair (alphabet : List K) {m N : ℕ} (M : Fin m → Fin N → K) :=
  checkedFind ((candidates alphabet N).product (candidates alphabet N))
    (checkedPairTest alphabet M)

@[simp] theorem checkedSearchPair_fst (alphabet : List K) {m N : ℕ}
    (M : Fin m → Fin N → K) :
    (checkedSearchPair alphabet M).1 = searchPair alphabet M := by
  simp [checkedSearchPair, searchPair]

theorem checkedSearchPair_count_le (alphabet : List K) (hq : 0 < alphabet.length)
    {m N : ℕ} (M : Fin m → Fin N → K) :
    (checkedSearchPair alphabet M).2 ≤
      (N + 1)^2 * alphabet.length ^ (2 * N * N) *
        ((N + 10) * (alphabet.length ^ N + 1)^3) := by
  apply (checkedFind_count_le _ _ _ (fun c _ => checkedPairTest_count_le alphabet hq M c)).trans
  exact Nat.mul_le_mul_right _ (pair_candidates_length_le alphabet hq N)

end SubexponentialSAT.Subexp.BlockSearch

end OAI.Algorithms
