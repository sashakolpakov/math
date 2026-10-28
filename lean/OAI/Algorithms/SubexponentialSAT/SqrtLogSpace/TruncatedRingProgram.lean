import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRing
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramValidity
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/
section NativeValidity
structure Good {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (a : List (Product.Entry n B d)) : Prop where
  valid : ∀ x ∈ a, Product.ValidKey vars u J x.1
  nodup : (Squarefree.Sparse.keys a).Nodup

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

theorem decoded_valid {R : Type*} [CommRing R]
    {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (f : RingProgram.Code (Word B) d → R) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f a) :=
  Product.decoded_valid f vars u J a h.valid

theorem length_le {a : List (Product.Entry n B d)} (h : Good vars u J a) :
    a.length ≤ u*J*(Squarefree.Sparse.supportUniverse vars J).card := by
  have hv := h.decoded_valid (fun _ => (0 : ℤ))
  have hn : (Squarefree.Sparse.keys (Dictionary.denoteTable (fun _ => (0 : ℤ)) a)).Nodup := by
    simpa only [Dictionary.denoteTable_keys] using h.nodup
  simpa only [Dictionary.denoteTable,List.length_map] using hv.length_le hn

theorem bytes_length_le {a : List (Product.Entry n B d)} (h : Good vars u J a) :
    (Product.bytes a).length ≤
      u*J*(Squarefree.Sparse.supportUniverse vars J).card * (2*(u+J+n)+2*(d*B)+2) := by
  exact (Product.bytes_length_le a (u+J+n)
    (fun x hx => Squarefree.encodeIndex_length_le x.1 (h.valid x hx).1)).trans
      (Nat.mul_le_mul_right _ h.length_le)
end Good

/-- The native constant keeps its origin record exactly at positive cutoffs. -/
theorem constant_good {n B d : ℕ} (u J : ℕ)
    (c : RingProgram.Code (Word B) d) :
    Good (n := n) ∅ u J (Squarefree.Sparse.constant u J c) := by
  by_cases h : 0 < u ∧ 0 < J
  · constructor
    · intro a ha
      simp only [Squarefree.Sparse.constant, ite_eq_left h, List.mem_singleton] at ha
      subst a
      simp [Product.ValidKey, Squarefree.Index.Kept, Squarefree.Index.Valid,
        Squarefree.Index.origin, h.1, h.2]
    · simp [Squarefree.Sparse.constant, h, Squarefree.Sparse.keys]
  · simpa only [Squarefree.Sparse.constant, ite_eq_right h] using
      (Good.nil (n := n) (B := B) (d := d) (vars := ∅) (u := u) (J := J))

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (vars : Finset (Fin n)) (u J : ℕ)

 theorem scaled_good (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (h : Good vars u J a) :
    Good vars u J (Squarefree.ScaleProgram.scaled p t M cache table c a) := by
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact h.valid y hy
  · exact Squarefree.ScaleProgram.scaled_nodup p t M cache table c a h.nodup

theorem normalize_good (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : ∀ x ∈ source, Product.ValidKey vars u J x.1) (hi : Good vars u J seed) :
    Good vars u J (Normalize.run p t M cache source seed) :=
  ⟨Normalize.run_preserves_keys p t M cache _ source seed hs hi.valid,
    Normalize.run_nodup p t M cache source seed hi.nodup⟩

theorem product_good (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good vars u J left) (hr : Good vars u J right) :
    Good vars u J (Product.run p t M cache table u J left right []) :=
  ⟨Product.run_valid p t M cache table vars u J left right [] hl.valid hr.valid (by simp),
    Product.run_nodup p t M cache table u J left right [] (by simp [Squarefree.Sparse.keys])⟩


end NativeValidity

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable section

noncomputable def rawDenote {R : Type*} [CommRing R] {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (a : List (Product.Entry n B d)) :
    Squarefree.Jet (Fin n) R := Squarefree.Sparse.denote (Dictionary.denoteTable f a)


section NativeDenotation
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (htable : ∀ i j, basis i * basis j =
  ∑ k, scalar (wordValue p t (table i j k)) * basis k)
local notation "f" => RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
local notation "D" => rawDenote (n := n) f
 theorem normalize_denote (source seed : List (Product.Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    D (Normalize.run p t M cache source seed) = D source + D seed :=
  Normalize.run_decode p t M cache scalar basis Squarefree.Sparse.atom
    Squarefree.Sparse.atom_zero Squarefree.Sparse.atom_add source seed hn

include htable in
theorem scale_denote (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) :
    D (Squarefree.ScaleProgram.scaled p t M cache table c a) = Squarefree.Sparse.atom Squarefree.Index.origin (f c) * D a :=
  Squarefree.ScaleProgram.denote_scaled p t M cache scalar basis table htable c a

include htable in
theorem product_denote (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d)) :
    D (Product.run p t M cache table u J left right []) =
      Squarefree.canonical u J (D left * D right) := by
  have h := Product.run_denote p t M cache scalar basis table htable u J left right []
    (by simp [Squarefree.Sparse.keys])
  simpa only [rawDenote,Dictionary.denoteTable,List.map_nil,Squarefree.Sparse.denote,
    Squarefree.Sparse.decode,add_zero] using h


end NativeDenotation

/-- The semantic projection for already-specialized correction variables. -/
def jetProjection (u J : ℕ) : Squarefree.Jet V R →+* Dense R u J :=
  (Dense.ofPolynomial u J).comp (Squarefree.evalJet (fun _ => 0) (by simp))

@[simp] theorem jetProjection_canonical (u J : ℕ) (P : Squarefree.Jet V R) :
    jetProjection u J (Squarefree.canonical u J P) = jetProjection u J P := by
  ext i j
  simp [jetProjection, Squarefree.coeff_evalJet, Squarefree.coeff_canonical, i.isLt, j.isLt]

@[simp] theorem jetProjection_jetScalar (u J : ℕ) (P : Moments.ScalarJet R) :
    jetProjection (V := V) u J (Moments.jetScalar P) = Dense.ofPolynomial u J P := by
  ext i j
  simp only [jetProjection, RingHom.comp_apply, Dense.coeff_ofPolynomial,
    Squarefree.coeff_evalJet, Moments.jetScalar, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  change Squarefree.evalHom (fun _ : V => 0) (by simp)
    (Squarefree.monomial ∅ ((P.coeff i.val).coeff j.val)) = (P.coeff i.val).coeff j.val
  simp [Squarefree.weight]

/-- Decode an actual finite native dictionary into the dense ring. -/
def rawValue {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) (a : List (Product.Entry n B d)) : Dense R u J :=
  jetProjection u J (rawDenote f a)

@[simp] theorem rawValue_nil {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) : rawValue (n := n) u J f [] = 0 := by
  simp [rawValue, rawDenote, Dictionary.denoteTable, Squarefree.Sparse.denote,
    Squarefree.Sparse.decode]

/-- An actual decoded unit represents the neutral factor, including zero cutoffs. -/
theorem rawValue_constant_one {R : Type*} [CommRing R] {n B d : ℕ}
    (u J : ℕ) (f : RingProgram.Code (Word B) d → R)
    (c : RingProgram.Code (Word B) d) (hc : f c = 1) :
    rawValue (n := n) u J f (Squarefree.Sparse.constant u J c) = 1 := by
  have hmap : Dictionary.denoteTable f (Squarefree.Sparse.constant (V := Fin n) u J c) =
      Squarefree.Sparse.constant u J (f c) := by
    by_cases h : 0 < u ∧ 0 < J <;>
      simp [Squarefree.Sparse.constant, h, Dictionary.denoteTable]
  change jetProjection u J (Squarefree.Sparse.denote _) = 1
  rw [hmap, hc, Squarefree.Sparse.denote_constant, Squarefree.Sparse.atom_origin_one,
    jetProjection_canonical, map_one]

theorem eval_zero_eq_coeff (P : Squarefree.Poly V R) :
    Squarefree.evalHom (fun _ => 0) (by simp) P = Squarefree.coeff ∅ P := by
  classical
  rw [← MonoidAlgebra.sum_coeff_single P]
  generalize P.coeff = q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [Finsupp.sum_add_index (by simp) (by simp)]
      simp only [map_add, ha, hb, Squarefree.coeff_add]
  | single s c =>
      rw [Finsupp.sum_single_index (by simp)]
      change Squarefree.evalHom (fun _ => 0) (by simp) (Squarefree.monomial s.vars c) =
        Squarefree.coeff ∅ (Squarefree.monomial s.vars c)
      rw [Squarefree.eval_monomial, Squarefree.coeff_monomial]
      by_cases hs : s.vars = ∅
      · simp [Squarefree.weight, hs]
      · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have hz : Squarefree.weight (fun _ : V => (0 : R)) s.vars = 0 :=
          Finset.prod_eq_zero hv rfl
        simp [hz, hs]

theorem rawValue_coeff {n B d u J : ℕ}
    (f : RingProgram.Code (Word B) d → R) (a : List (Product.Entry n B d))
    (i : Fin u) (j : Fin J) :
    ((rawValue u J f a).coeff i).coeff j =
      Squarefree.Sparse.fetch ⟨i.val, j.val, ∅⟩ (Dictionary.denoteTable f a) := by
  simp only [rawValue, jetProjection, RingHom.comp_apply, Dense.coeff_ofPolynomial,
    Squarefree.coeff_evalJet, eval_zero_eq_coeff]
  exact Squarefree.Sparse.jetCoeff_denote ⟨i.val, j.val, ∅⟩ _

/-- The existing native additive readout is exactly the dense marker sum. -/
theorem readout_codes_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (u J : ℕ) (entries : List (Product.Entry n (baseWidth p t) d))
    (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup)
    (hz : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis zero = 0) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Truncated.ofPolynomial J (PolynomialAlgorithm.denote
      ((MomentsReadoutProgram.outputCodes p t M cache entries u zero 0 J).map f)) =
      Dense.readout (rawValue u J f entries) := by
  dsimp only
  rw [MomentsReadoutProgram.outputCodes_denote p t M cache scalar basis entries u J zero hn hz]
  ext z
  rw [Truncated.coeff_ofPolynomial, PolynomialAlgorithm.coeff_denote,
    Moments.outputCoefficients, Moments.coeff_tabulate, ite_eq_left z.isLt,
    Dense.coeff_readout]
  simp only [rawValue_coeff]
  exact (Fin.sum_univ_eq_sum_range
    (fun i => Squarefree.Sparse.fetch ⟨i, z.val, ∅⟩
      (Dictionary.denoteTable
        (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) entries)) u).symm

theorem normalize_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R) (u J : ℕ)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawValue u J f (Normalize.run p t M cache source seed) =
      rawValue u J f source + rawValue u J f seed := by
  dsimp only [rawValue]
  rw [normalize_denote p t M cache scalar basis source seed hn, map_add]

theorem product_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawValue u J f (Product.run p t M cache table u J left right []) =
      rawValue u J f left * rawValue u J f right := by
  dsimp only [rawValue]
  rw [product_denote p t M cache scalar basis table htable u J,
    jetProjection_canonical, map_mul]

theorem scaling_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawValue u J f (Squarefree.ScaleProgram.scaled p t M cache table c a) =
      jetProjection (V := Fin n) u J (Squarefree.Sparse.atom Squarefree.Index.origin (f c)) * rawValue u J f a := by
  dsimp only [rawValue]
  rw [scale_denote p t M cache scalar basis table htable c a, map_mul]

/-- A physically represented negative unit supplies the finite-difference sign. -/
theorem negation_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
      minusOne = -1)
    (a : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawValue u J f (Squarefree.ScaleProgram.scaled p t M cache table minusOne a) =
      -rawValue u J f a := by
  dsimp only [rawValue]
  have h := Squarefree.ScaleProgram.denote_neg p t M cache scalar basis table htable
    minusOne hminus a
  change rawDenote _ _ = -rawDenote _ a at h
  rw [h]
  exact map_neg (jetProjection (V := Fin n) (R := R) u J) _

end

omit [DecidableEq V] in
/-- Empty formal support has at most one possible support, also when `J = 0`. -/
theorem empty_support_card_le (J : ℕ) :
    (Squarefree.Sparse.supportUniverse (∅ : Finset V) J).card ≤ 1 := by
  calc
    _ ≤ ((∅ : Finset V).powerset).card := Finset.card_filter_le _ _
    _ = 1 := by simp

theorem empty_key_vars {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) (x : Product.Entry n B d) (hx : x ∈ a) : x.1.vars = ∅ :=
  Finset.subset_empty.mp (ha.valid x hx).2.2

theorem empty_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) : a.length ≤ u * J := by
  exact ha.length_le.trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (u * J)
      (empty_support_card_le (V := Fin n) J))

theorem empty_bytes_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) :
    (Product.bytes a).length ≤ u * J * (2 * (u + J + n) + 2 * (d * B) + 2) := by
  exact (Product.bytes_length_le a (u + J + n)
    (fun x hx => Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1)).trans
      (Nat.mul_le_mul_right _ (empty_length_le ha))

private theorem stackBits_le_uniform {s : ℕ} (stk : Fin s → List Bool) (bound : ℕ)
    (h : ∀ i, (stk i).length ≤ bound) : stackBits stk ≤ s * bound := by
  calc
    _ ≤ ∑ _ : Fin s, bound := Finset.sum_le_sum (fun i _ => h i)
    _ = s * bound := by simp

private def productStoreBits (s : Product.Store) : ℕ :=
  s.keySource.length + s.keyLeft.length + s.keyUCap.length + s.keyZCap.length +
    s.mapped.length + s.modulus.length + s.width.length + s.zero.length + s.table.length +
    s.normalSource.length + s.scaleSource.length + s.scalar.length + s.scaled.length +
    s.degree.length + s.left.length + s.right.length + s.acc.length + s.key.length +
    s.coeff.length + s.uCap.length + s.zCap.length + s.reversedCoeff.length + s.normalCount.length

private theorem length_ite_le (p : Prop) [Decidable p] (xs ys : List Bool) (bound : ℕ)
    (hx : xs.length ≤ bound) (hy : ys.length ≤ bound) :
    (if p then xs else ys).length ≤ bound := by
  split <;> assumption

private theorem product_tapes_length_le (s : Product.Store) (i : Fin 56) :
    (Product.tapes s i).length ≤ productStoreBits s := by
  dsimp only [Product.tapes]
  repeat' apply length_ite_le
  all_goals simp only [productStoreBits, List.length_nil]; omega

/-- The concrete product input includes all three structure-constant indices,
the two coefficient arrays and the marker/Taylor controls. -/
theorem product_input_bits_le (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good ∅ u J left) (hr : Good ∅ u J right) (regs : Fin 8 → Bool) :
    dataBits ((Product.state regs
      (Product.working (Product.environment p t M cache table degree width u J)
        left right [])).withPC (some Product.program.entry)) ≤
      56 * (M.bits.length + 2 * baseWidth p t + d ^ 3 * baseWidth p t + d +
        2 * (u * J * (2 * (u + J + n) + 2 * (d * baseWidth p t) + 2)) + u + J) := by
  have hlb := empty_bytes_length_le hl
  have hrb := empty_bytes_length_le hr
  change (Normalize.bytes Squarefree.encodeIndex left).length ≤ _ at hlb
  change (Normalize.bytes Squarefree.encodeIndex right).length ≤ _ at hrb
  apply stackBits_le_uniform
  intro i
  apply (product_tapes_length_le _ i).trans
  dsimp only [productStoreBits, Product.working, Product.environment, Product.idle]
  have hempty : Product.bytes ([] : List (Product.Entry n (baseWidth p t) d)) = [] := rfl
  simp only [hempty, List.length_nil, List.length_replicate,
    RingTriple.tableEncoding_length, hw, hd, cache.zero.property]
  omega

def additionBudget (n B d u J : ℕ) : ℕ :=
  (u * J) * (220 * (2 * (u * J) + 1) * (n + u + J + d * B + 1) +
    Dictionary.codeBranchBudget B d + 2) + 3

def normalizationBudget (n B d u J N : ℕ) : ℕ :=
  N * (220 * (N + u * J + 1) * (n + u + J + d * B + 1) +
    Dictionary.codeBranchBudget B d + 2) + 3

/-- Specialization can create equal keys; normalization accepts those collisions.
The source bound counts every emitted record, before equal keys are merged. -/
theorem normalization_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J N : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : ∀ x ∈ source, Product.ValidKey ∅ u J x.1)
    (hN : source.length ≤ N) (hseed : Good ∅ u J seed)
    (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let start := (Normalize.state regs M.bits width degree (Product.bytes seed)
      (Product.bytes source)).withPC (some Normalize.program.entry)
    let result := Normalize.run p t M cache source seed
    ∃ steps rr,
      steps ≤ normalizationBudget n (baseWidth p t) d u J N ∧
      Trace Normalize.program steps start
        ((Normalize.state rr M.bits width degree (Product.bytes result) []).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace Normalize.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + normalizationBudget n (baseWidth p t) d u J N := by
  dsimp only
  have hr := empty_length_le hseed
  have hs : Normalize.KeyBound Squarefree.encodeIndex (n + u + J) source := by
    intro x hx
    have h := Squarefree.encodeIndex_length_le x.1 (hsource x hx).1
    omega
  have hi : Normalize.KeyBound Squarefree.encodeIndex (n + u + J) seed := by
    intro x hx
    have h := Squarefree.encodeIndex_length_le x.1 (hseed.valid x hx).1
    omega
  have hc := Normalize.work_le p t M cache Squarefree.encodeIndex (n + u + J)
    (N + u * J) source seed hs hi (by omega)
  have hbudget : Normalize.work p t M cache Squarefree.encodeIndex source seed + 2 ≤
      normalizationBudget n (baseWidth p t) d u J N := by
    have hm := Nat.mul_le_mul_right
      (220 * (N + u * J + 1) * (n + u + J + d * baseWidth p t + 1) +
        Dictionary.codeBranchBudget (baseWidth p t) d + 2) hN
    unfold normalizationBudget
    omega
  obtain ⟨rr, steps, hsteps, htrace⟩ := Normalize.program_run p t M cache
    Squarefree.encodeIndex Squarefree.encodeIndex_injective source seed regs width degree hd hw
  have hb := hsteps.trans hbudget
  refine ⟨steps, rr, hb, htrace,
    normalize_good p t M cache ∅ u J source seed hsource hseed, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound Normalize.program le_rfl prefixSteps intermediate
    (hprefix.trans hb) hp

/-- Native addition normalizes one bounded array into another bounded array. -/
theorem addition_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let start := (Normalize.state regs M.bits width degree (Product.bytes seed)
      (Product.bytes source)).withPC (some Normalize.program.entry)
    let result := Normalize.run p t M cache source seed
    ∃ steps rr,
      steps ≤ additionBudget n (baseWidth p t) d u J ∧
      Trace Normalize.program steps start
        ((Normalize.state rr M.bits width degree (Product.bytes result) []).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace Normalize.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + additionBudget n (baseWidth p t) d u J := by
  dsimp only
  have hl := empty_length_le hsource
  have hr := empty_length_le hseed
  have hbound : ∀ a : List (Product.Entry n (baseWidth p t) d), Good ∅ u J a →
      Normalize.KeyBound Squarefree.encodeIndex (n + u + J) a := by
    intro a ha x hx
    have h := Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1
    omega
  have hc := Normalize.work_le p t M cache Squarefree.encodeIndex (n + u + J)
    (2 * (u * J)) source seed (hbound source hsource) (hbound seed hseed) (by omega)
  have hbudget : Normalize.work p t M cache Squarefree.encodeIndex source seed + 2 ≤
      additionBudget n (baseWidth p t) d u J := by
    have hm := Nat.mul_le_mul_right
      (220 * (2 * (u * J) + 1) * (n + u + J + d * baseWidth p t + 1) +
        Dictionary.codeBranchBudget (baseWidth p t) d + 2) hl
    unfold additionBudget
    omega
  obtain ⟨rr, steps, hsteps, htrace⟩ := Normalize.program_run p t M cache
    Squarefree.encodeIndex Squarefree.encodeIndex_injective source seed regs width degree hd hw
  have hb := hsteps.trans hbudget
  refine ⟨steps, rr, hb, htrace,
    normalize_good p t M cache ∅ u J source seed hsource.valid hseed, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound Normalize.program le_rfl prefixSteps intermediate
    (hprefix.trans hb) hp

def scalingBudget (n B d u J : ℕ) : ℕ :=
  (u * J) * (40000 * (d + 1) ^ 3 * (B + 1) ^ 2 + 35 * (d * B) +
    7 * d + 22 * (n + u + J) + 57) + 6

/-- Scalar multiplication also implements signs using the cached negative unit. -/
theorem scaling_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good ∅ u J a)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) :
    let e := Squarefree.ScaleProgram.environment p t M cache table c degree width
    let start := (Squarefree.ScaleProgram.state regs
      (Squarefree.ScaleProgram.idle e (Product.bytes a) [])).withPC
        (some Squarefree.ScaleProgram.program.entry)
    let result := Squarefree.ScaleProgram.scaled p t M cache table c a
    ∃ steps rr,
      steps ≤ scalingBudget n (baseWidth p t) d u J ∧
      Trace Squarefree.ScaleProgram.program steps start
        ((Squarefree.ScaleProgram.state rr
          {Squarefree.ScaleProgram.idle e [] [] with output := Product.bytes result}).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace Squarefree.ScaleProgram.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + scalingBudget n (baseWidth p t) d u J := by
  dsimp only
  have hlen := empty_length_le ha
  have hc := Squarefree.ScaleProgram.budget_le Squarefree.encodeIndex a (n + u + J) (by
    intro x hx
    have h := Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1
    omega)
  have hbudget : Squarefree.ScaleProgram.budget Squarefree.encodeIndex a + 1 ≤
      scalingBudget n (baseWidth p t) d u J := by
    apply hc.trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 6
  obtain ⟨rr, steps, hsteps, htrace⟩ := Squarefree.ScaleProgram.program_runsIn p t M cache hz
    table c degree width hd hw Squarefree.encodeIndex a regs
  have hb := hsteps.trans hbudget
  refine ⟨steps, rr, hb, htrace, scaled_good p t M cache table ∅ u J c a ha, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound Squarefree.ScaleProgram.program le_rfl
    prefixSteps intermediate (hprefix.trans hb) hp

/-- Polynomial in dimensions, coefficient width and ambient input length. -/
def productBudget (n B d u J : ℕ) : ℕ :=
  (u * J) * (Product.stepEnvelope B d n u J ((u * J) ^ 2) (u * J) + 2) + 3

theorem product_work_le (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good ∅ u J left) (hr : Good ∅ u J right) :
    Product.work p t M cache table u J left right [] + 2 ≤
      productBudget n (baseWidth p t) d u J := by
  have hleft := empty_length_le hl
  have hright := empty_length_le hr
  have hw := Product.work_le p t M cache table u J ((u * J) ^ 2) left right []
    (fun a ha => (hl.valid a ha).1) (fun b hb => (hr.valid b hb).1)
    (by simp [Normalize.KeyBound]) (by simpa [pow_two] using Nat.mul_le_mul hleft hright)
  have henv : Product.stepEnvelope (baseWidth p t) d n u J ((u * J) ^ 2) right.length ≤
      Product.stepEnvelope (baseWidth p t) d n u J ((u * J) ^ 2) (u * J) := by
    dsimp [Product.stepEnvelope]
    gcongr
  have htotal := Nat.mul_le_mul hleft (Nat.add_le_add_right henv 2)
  unfold productBudget
  omega

/-- Actual multiplication, its clean return, and every local source prefix.
The initial stack sum explicitly includes every persistent cache and both inputs. -/
theorem product_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good ∅ u J left) (hr : Good ∅ u J right) (regs : Fin 8 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    let start := (Product.state regs (Product.working e left right [])).withPC
      (some Product.program.entry)
    let result := Product.run p t M cache table u J left right []
    ∃ steps rr,
      steps ≤ productBudget n (baseWidth p t) d u J ∧
      Trace Product.program steps start
        ((Product.state rr (Product.working e [] right result)).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace Product.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          dataBits start + productBudget n (baseWidth p t) d u J := by
  dsimp only
  obtain ⟨rr, steps, hsteps, htrace⟩ :=
    Product.program_run_seed p t M cache hz table degree width hd hw u J left right [] regs
  have hb := hsteps.trans (product_work_le p t M cache table u J left right hl hr)
  refine ⟨steps, rr, hb, htrace, product_good p t M cache table ∅ u J left right hl hr, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound Product.program le_rfl prefixSteps intermediate
    (hprefix.trans hb) hp

/-- The readout uses only `u * J` records and returns exactly `J` coefficient words. -/
theorem readout_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let start := (MomentsReadoutProgram.wideState regs
      (Dictionary.inputTape M.bits width degree encoded [] [])
      (MomentsReadoutProgram.inputHigh (RingProgram.flat zero) marker taylor shape)).withPC
        (some MomentsReadoutProgram.program.entry)
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    let budget := MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J
      (n + u + J) (u * J)
    ∃ steps rr,
      steps ≤ budget ∧
      Trace MomentsReadoutProgram.program steps start
        ((MomentsReadoutProgram.wideState rr
          {Dictionary.inputTape M.bits width degree encoded [] [] with out := bits}
          (MomentsReadoutProgram.inputHigh (RingProgram.flat zero) marker taylor shape)).withPC none) ∧
      bits.length = J * (d * baseWidth p t) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace MomentsReadoutProgram.program prefixSteps start intermediate →
        ∀ i, (intermediate.stacks i).length ≤ dataBits start + budget := by
  dsimp only
  obtain ⟨rr, steps, hsteps, htrace⟩ :=
    MomentsReadoutProgram.program_runsIn_polynomial p t M cache entries zero regs width degree
      marker taylor shape (n + u + J) hd hw hs (by
        intro a ha
        have h := Squarefree.encodeIndex_length_le a.1 (he.valid a ha).1
        omega)
  rw [hu, hJ] at hsteps htrace
  have hbudget : MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J
      (n + u + J) entries.length ≤
      MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J (n + u + J) (u * J) := by
    have hlen := empty_length_le he
    dsimp [MomentsReadoutProgram.uniformReadoutBudget, MomentsReadoutProgram.uniformSlotBudget]
    gcongr
  have hb := hsteps.trans hbudget
  refine ⟨steps, rr, hb, htrace, MomentsReadoutProgram.outputBits_length _ _ _ _ _ _ _ _ _, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound MomentsReadoutProgram.program le_rfl prefixSteps intermediate
    (hprefix.trans hb) hp

/-- A common explicit polynomial majorant for every local arithmetic service.
`N` counts unnormalized specialized records; it need not be at most `u * J`. -/
def localBudget (n B d u J N : ℕ) : ℕ :=
  normalizationBudget n B d u J N + additionBudget n B d u J +
    scalingBudget n B d u J + productBudget n B d u J +
    MomentsReadoutProgram.uniformReadoutBudget B d n u J (n + u + J) (u * J)

private theorem localBudget_mono (n B d u J N a : ℕ)
    (hn : n ≤ a) (hB : B ≤ a) (hd : d ≤ a) (hu : u ≤ a) (hJ : J ≤ a) (hN : N ≤ a) :
    localBudget n B d u J N ≤ localBudget a a a a a a := by
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  gcongr

/-- The degree and constant are fixed before every runtime dimension. -/
theorem localBudget_le (n B d u J N : ℕ) :
    localBudget n B d u J N ≤ 3000000 * (n + B + d + u + J + N + 1) ^ 10 := by
  let a := n + B + d + u + J + N + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  refine (localBudget_mono n B d u J N a (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega)).trans ?_
  change localBudget a a a a a a ≤ 3000000 * a ^ 10
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h5 : a ^ 5 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h6 : a ^ 6 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h7 : a ^ 7 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h8 : a ^ 8 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h9 : a ^ 9 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  ring_nf
  omega

theorem normalizationBudget_le_local (n B d u J N : ℕ) :
    normalizationBudget n B d u J N ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

theorem additionBudget_le_local (n B d u J N : ℕ) :
    additionBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

theorem scalingBudget_le_local (n B d u J N : ℕ) :
    scalingBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

theorem productBudget_le_local (n B d u J N : ℕ) :
    productBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

theorem readoutBudget_le_local (n B d u J N : ℕ) :
    MomentsReadoutProgram.uniformReadoutBudget B d n u J (n + u + J) (u * J) ≤
      localBudget n B d u J N := by
  unfold localBudget
  omega

/-- Additive readout has a fixed degree-six bound. -/
theorem readoutBudget_polynomial (n B d u J : ℕ) :
 MomentsReadoutProgram.uniformReadoutBudget B d n u J (n+u+J) (u*J) ≤30000*(n+B+d+u+J+1)^6 := by
 let a := n+B+d+u+J+1
 have ha : 1≤a := by dsimp [a]; omega
 have hm : MomentsReadoutProgram.uniformReadoutBudget B d n u J (n+u+J) (u*J) ≤MomentsReadoutProgram.uniformReadoutBudget a a a a a (a+a+a) (a*a) := by
  have hn : n≤a := by dsimp [a]; omega
  have hB : B≤a := by dsimp [a]; omega
  have hd : d≤a := by dsimp [a]; omega
  have hu : u≤a := by dsimp [a]; omega
  have hJ : J≤a := by dsimp [a]; omega
  dsimp [MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  gcongr
 refine hm.trans ?_
 change MomentsReadoutProgram.uniformReadoutBudget a a a a a (a+a+a) (a*a) ≤30000*a^6
 have h0 : 1≤a^6 := Nat.one_le_pow 6 a ha
 have h1 : a≤a^6 := by simpa using pow_le_pow_right' ha (show 1≤6 by decide)
 have h2 : a^2≤a^6 := pow_le_pow_right' ha (by decide)
 have h3 : a^3≤a^6 := pow_le_pow_right' ha (by decide)
 have h4 : a^4≤a^6 := pow_le_pow_right' ha (by decide)
 have h5 : a^5≤a^6 := pow_le_pow_right' ha (by decide)
 dsimp [MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
 ring_nf
 omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
