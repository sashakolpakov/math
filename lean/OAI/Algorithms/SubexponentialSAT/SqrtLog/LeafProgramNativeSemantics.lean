import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramMeaning
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramValidity
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramScalarRow
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingSource

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native

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

variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))

include hone in
theorem literal_good (payload : List (Product.Entry n (baseWidth p t) d))
    (hp : Good vars u J payload) (positive : Bool) :
    Good vars u J (LiteralCallback.value p t M cache table minusOne one payload positive) := by
  cases positive
  · exact hp
  · exact normalize_good p t M cache vars u J _ one
      (scaled_good p t M cache table vars u J minusOne payload hp).valid hone

include hone hi in
theorem step_good (l : SAT.Literal (Fin n))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (Clause.step p t M cache table minusOne one incidence u J l acc) :=
  product_good p t M cache table vars u J acc _ ha
    (literal_good p t M cache table vars u J minusOne one hone _ (hi l.variable) l.positive)

include hone hi in
theorem clause_fold_good (ls : List (SAT.Literal (Fin n)))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (DynamicFold.value
      (Clause.step p t M cache table minusOne one incidence u J) ls acc) := by
  induction ls generalizing acc with
  | nil => exact ha
  | cons l ls ih => exact ih _ (step_good p t M cache table vars u J minusOne one incidence hone hi l acc ha)

include hone hi in
theorem row_step_good (w : Row.WeightedClause n (baseWidth p t) d)
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (Row.value p t M cache table minusOne one incidence u J w acc) :=
  normalize_good p t M cache vars u J _ acc
    (scaled_good p t M cache table vars u J w.scalar _
      (clause_fold_good p t M cache table vars u J minusOne one incidence hone hi w.literals one hone)).valid ha

include hone hi in
theorem row_fold_good (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    Good vars u J (DynamicFold.value
      (Row.value p t M cache table minusOne one incidence u J) ws acc) := by
  induction ws generalizing acc with
  | nil => exact ha
  | cons w ws ih => exact ih _ (row_step_good p t M cache table vars u J minusOne one incidence hone hi w acc ha)

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Denotation of the concrete raw row recurrence used by the native program. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

noncomputable def rawDenote {R : Type*} [CommRing R] {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (a : List (Product.Entry n B d)) :
    Squarefree.Jet (Fin n) R := Squarefree.Sparse.denote (Dictionary.denoteTable f a)

def sourceTerms {R : Type*} {n B d : ℕ} (f : RingProgram.Code (Word B) d → R)
    (ws : List (Row.WeightedClause n B d)) : SparseRow (Fin n) R :=
  ws.map (fun w => (f w.scalar,w.literals))

/-- A clause fold only reads the variables of its listed literals. -/
theorem clauseFold_congr {A V : Type*} (alg : Algebra A) (x y : V → A)
    (ls : List (SAT.Literal V))
    (h : ∀ l ∈ ls, x l.variable = y l.variable) (acc : A) :
    clauseFoldValue alg x ls acc = clauseFoldValue alg y ls acc := by
  induction ls generalizing acc with
  | nil => rfl
  | cons l ls ih =>
    have hl : literalValue alg x l = literalValue alg y l := by
      simp only [literalValue,h l (by simp)]
    change clauseFoldValue alg x ls (alg.mul acc (literalValue alg x l)) =
      clauseFoldValue alg y ls (alg.mul acc (literalValue alg y l))
    rw [hl]
    exact ih (fun a ha => h a (by simp [ha])) _

variable {R : Type*} [CommRing R]
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
    D (Squarefree.ScaleProgram.scaled p t M cache table c a) = scalarJet (f c) * D a :=
  Squarefree.ScaleProgram.denote_scaled p t M cache scalar basis table htable c a

include htable in
theorem product_denote (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d)) :
    D (Product.run p t M cache table u J left right []) =
      Squarefree.canonical u J (D left * D right) := by
  have h := Product.run_denote p t M cache scalar basis table htable u J left right []
    (by simp [Squarefree.Sparse.keys])
  simpa only [rawDenote,Dictionary.denoteTable,List.map_nil,Squarefree.Sparse.denote,
    Squarefree.Sparse.decode,add_zero] using h

include htable in
theorem scale_denote_canonical (vars : Finset (Fin n)) (u J : ℕ)
    (c : RingProgram.Code (Word (baseWidth p t)) d)
    (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J a) :
    D (Squarefree.ScaleProgram.scaled p t M cache table c a) =
      (squarefreeAlgebra u J).mul (Squarefree.canonical u J (scalarJet (f c))) (D a) := by
  let stored : Moments.Stored (R := R) vars u J :=
    ⟨Dictionary.denoteTable f a,ha.decoded_valid f,
      by simpa only [Dictionary.denoteTable_keys] using ha.nodup⟩
  rw [scale_denote p t M cache scalar basis table htable]
  simpa only [Moments.Stored.denote,Moments.Stored.scale,Squarefree.Sparse.denote_scale,
    scalarJet,stored,rawDenote] using stored_scale_correct (f c) stored

variable (vars : Finset (Fin n)) (u J : ℕ)
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))
variable (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
variable (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) one =
  Squarefree.canonical u J 1)

include htable hone hminus honeval in
 theorem literal_denote (payload : List (Product.Entry n (baseWidth p t) d)) (positive : Bool) :
    D (LiteralCallback.value p t M cache table minusOne one payload positive) =
      if positive then Squarefree.canonical u J 1 + -(D payload) else D payload := by
  cases positive
  · rfl
  · change D (Normalize.run p t M cache _ one) = _
    rw [normalize_denote p t M cache scalar basis _ one hone.nodup]
    have hn := Squarefree.ScaleProgram.denote_neg p t M cache scalar basis table htable
      minusOne hminus payload
    change D (Squarefree.ScaleProgram.scaled p t M cache table minusOne payload) = -D payload at hn
    rw [hn,honeval,add_comm]
    all_goals rfl

include htable hone hminus honeval in
theorem step_denote (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) :
    D (Clause.step p t M cache table minusOne one incidence u J l acc) =
      (squarefreeAlgebra u J).mul (D acc)
        (literalValue (squarefreeAlgebra u J) (fun v => D (incidence v)) l) := by
  unfold Clause.step LiteralCallback.result
  rw [product_denote p t M cache scalar basis table htable]
  rw [literal_denote p t M cache scalar basis table htable vars u J minusOne one hone hminus honeval]
  all_goals rfl

include htable hone hminus honeval in
theorem clause_fold_denote (ls : List (SAT.Literal (Fin n)))
    (acc : List (Product.Entry n (baseWidth p t) d)) :
    D (DynamicFold.value (Clause.step p t M cache table minusOne one incidence u J) ls acc) =
      clauseFoldValue (squarefreeAlgebra u J) (fun v => D (incidence v)) ls (D acc) := by
  induction ls generalizing acc with
  | nil => rfl
  | cons l ls ih =>
    simp only [DynamicFold.value]
    rw [ih,step_denote p t M cache scalar basis table htable vars u J
      minusOne one incidence hone hminus honeval]
    rfl

variable (jet : Fin n → Squarefree.Jet (Fin n) R)
variable (hjet : ∀ v,
  rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) (incidence v) =
    Squarefree.canonical u J (jet v))

include htable hone hminus honeval hjet in
theorem clause_denote (w : Row.WeightedClause n (baseWidth p t) d) :
    D (Row.clauseValue p t M cache table minusOne one incidence u J w) =
      clauseValue (squarefreeAlgebra u J) (fun v => Squarefree.canonical u J (jet v)) w.literals := by
  unfold Row.clauseValue
  rw [clause_fold_denote p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval]
  simp_rw [hjet]
  rw [honeval]
  exact clauseFoldValue_projected_one (Squarefree.canonical u J)
    (Squarefree.canonical_mul u J) jet w.literals

include htable hone hminus honeval hjet in
/-- A marked clause uses this result directly, without an idempotent map. -/
theorem clause_polynomial (w : Row.WeightedClause n (baseWidth p t) d) :
    D (Row.clauseValue p t M cache table minusOne one incidence u J w) =
      Squarefree.canonical u J (MvPolynomial.eval jet (clausePolynomial (R := Squarefree.Jet (Fin n) R) w.literals)) := by
  rw [clause_denote p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval jet hjet]
  change clauseValue (projectedAlgebra (Squarefree.canonical u J))
    (fun v => Squarefree.canonical u J (jet v)) w.literals = _
  exact (clauseValue_projected (Squarefree.canonical u J) (Squarefree.canonical_mul u J)
    jet w.literals).trans (congrArg (Squarefree.canonical u J) (clauseValue_eq_eval jet w.literals))

include htable hone hminus honeval hjet in
/-- Direct clause-list form, used by the marked-clause factor. -/
theorem clause_list_polynomial (ls : List (SAT.Literal (Fin n))) :
    D (DynamicFold.value (Clause.step p t M cache table minusOne one incidence u J) ls one) =
      Squarefree.canonical u J (MvPolynomial.eval jet (clausePolynomial (R := Squarefree.Jet (Fin n) R) ls)) := by
  let w : Row.WeightedClause n (baseWidth p t) d := ⟨fun _ => cache.zero,ls⟩
  exact clause_polynomial p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval jet hjet w

include htable hone hi hminus honeval hjet in
theorem row_step_denote (w : Row.WeightedClause n (baseWidth p t) d)
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    D (Row.value p t M cache table minusOne one incidence u J w acc) =
      D acc + (squarefreeAlgebra u J).mul (Squarefree.canonical u J (scalarJet (f w.scalar)))
        (clauseValue (squarefreeAlgebra u J) (fun v => Squarefree.canonical u J (jet v)) w.literals) := by
  unfold Row.value
  rw [normalize_denote p t M cache scalar basis _ acc ha.nodup]
  rw [scale_denote_canonical p t M cache scalar basis table htable vars u J w.scalar
    (Row.clauseValue p t M cache table minusOne one incidence u J w)
    (clause_fold_good p t M cache table vars u J minusOne one incidence hone hi w.literals one hone)]
  rw [clause_denote p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval jet hjet]
  exact add_comm _ _

include htable hone hi hminus honeval hjet in
theorem row_fold_denote (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    D (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws acc) =
      rowFoldValue (squarefreeAlgebra u J) (fun c => Squarefree.canonical u J (scalarJet c))
        (fun v => Squarefree.canonical u J (jet v)) (sourceTerms f ws) (D acc) := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    simp only [DynamicFold.value]
    rw [ih _ (row_step_good p t M cache table vars u J minusOne one incidence hone hi w acc ha)]
    rw [row_step_denote p t M cache scalar basis table htable vars u J
      minusOne one incidence hone hi hminus honeval jet hjet w acc ha]
    rfl

include htable hone hi hminus honeval hjet in
/-- The exact executable raw result denotes the canonical source polynomial. -/
theorem row_denote (ws : List (Row.WeightedClause n (baseWidth p t) d)) :
    D (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws []) =
      Squarefree.canonical u J
        (MvPolynomial.eval jet (rowPolynomial (scalarJet (V := Fin n)) (sourceTerms f ws))) := by
  rw [row_fold_denote p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hi hminus honeval jet hjet ws [] Good.nil]
  exact scalar_rowFold_source u J jet (sourceTerms f ws)

include htable hone hminus honeval in
/-- Only the incidence rows referenced by this clause need the intended value. -/
theorem clause_denote_scoped (w : Row.WeightedClause n (baseWidth p t) d)
    (hs : ∀ l ∈ w.literals, D (incidence l.variable) = Squarefree.canonical u J (jet l.variable)) :
    D (Row.clauseValue p t M cache table minusOne one incidence u J w) =
      clauseValue (squarefreeAlgebra u J) (fun v => Squarefree.canonical u J (jet v)) w.literals := by
  unfold Row.clauseValue
  rw [clause_fold_denote p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval]
  rw [clauseFold_congr (squarefreeAlgebra u J) (fun v => D (incidence v))
    (fun v => Squarefree.canonical u J (jet v)) w.literals hs]
  rw [honeval]
  exact clauseFoldValue_projected_one (Squarefree.canonical u J)
    (Squarefree.canonical_mul u J) jet w.literals

include htable hone hminus honeval in
theorem clause_list_polynomial_scoped (ls : List (SAT.Literal (Fin n)))
    (hs : ∀ l ∈ ls, D (incidence l.variable) = Squarefree.canonical u J (jet l.variable)) :
    D (DynamicFold.value (Clause.step p t M cache table minusOne one incidence u J) ls one) =
      Squarefree.canonical u J (MvPolynomial.eval jet (clausePolynomial (R := Squarefree.Jet (Fin n) R) ls)) := by
  let w : Row.WeightedClause n (baseWidth p t) d := ⟨fun _ => cache.zero,ls⟩
  change D (Row.clauseValue p t M cache table minusOne one incidence u J w) = _
  rw [clause_denote_scoped p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval jet w hs]
  change clauseValue (projectedAlgebra (Squarefree.canonical u J))
    (fun v => Squarefree.canonical u J (jet v)) ls = _
  exact (clauseValue_projected (Squarefree.canonical u J) (Squarefree.canonical_mul u J)
    jet ls).trans (congrArg (Squarefree.canonical u J) (clauseValue_eq_eval jet ls))

include htable hone hi hminus honeval in
theorem row_step_denote_scoped (w : Row.WeightedClause n (baseWidth p t) d)
    (hs : ∀ l ∈ w.literals, D (incidence l.variable) = Squarefree.canonical u J (jet l.variable))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    D (Row.value p t M cache table minusOne one incidence u J w acc) =
      D acc + (squarefreeAlgebra u J).mul (Squarefree.canonical u J (scalarJet (f w.scalar)))
        (clauseValue (squarefreeAlgebra u J) (fun v => Squarefree.canonical u J (jet v)) w.literals) := by
  unfold Row.value
  rw [normalize_denote p t M cache scalar basis _ acc ha.nodup]
  rw [scale_denote_canonical p t M cache scalar basis table htable vars u J w.scalar
    (Row.clauseValue p t M cache table minusOne one incidence u J w)
    (clause_fold_good p t M cache table vars u J minusOne one incidence hone hi w.literals one hone)]
  rw [clause_denote_scoped p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hminus honeval jet w hs]
  exact add_comm _ _

include htable hone hi hminus honeval in
theorem row_fold_denote_scoped (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (hs : ∀ w ∈ ws, ∀ l ∈ w.literals,
      D (incidence l.variable) = Squarefree.canonical u J (jet l.variable))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    D (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws acc) =
      rowFoldValue (squarefreeAlgebra u J) (fun c => Squarefree.canonical u J (scalarJet c))
        (fun v => Squarefree.canonical u J (jet v)) (sourceTerms f ws) (D acc) := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    simp only [DynamicFold.value]
    rw [ih (fun a ha => hs a (by simp [ha])) _
      (row_step_good p t M cache table vars u J minusOne one incidence hone hi w acc ha)]
    rw [row_step_denote_scoped p t M cache scalar basis table htable vars u J
      minusOne one incidence hone hi hminus honeval jet w (hs w (by simp)) acc ha]
    rfl

include htable hone hi hminus honeval in
/-- Missing variables may have zero rows: only literals actually read by this
factor require the intended incidence semantics. -/
theorem row_denote_scoped (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (hs : ∀ w ∈ ws, ∀ l ∈ w.literals,
      D (incidence l.variable) = Squarefree.canonical u J (jet l.variable)) :
    D (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws []) =
      Squarefree.canonical u J
        (MvPolynomial.eval jet (rowPolynomial (scalarJet (V := Fin n)) (sourceTerms f ws))) := by
  rw [row_fold_denote_scoped p t M cache scalar basis table htable vars u J
    minusOne one incidence hone hi hminus honeval jet ws hs [] Good.nil]
  exact scalar_rowFold_source u J jet (sourceTerms f ws)

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Instantiation at the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

 def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) :=
  (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

theorem model_table_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (i j : Fin d) :
    RingBasis.basis (a.F t) i * RingBasis.basis (a.F t) j =
      ∑ k, SubexponentialSAT.LiftRing.of (a.F t) (wordValue 3 t (modelTable t a M cache i j k)) *
        RingBasis.basis (a.F t) k := by
  let _ : Fact (1 < 3^t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  rw [RingBasis.basis_mul (a.F t) (a.F_monic t ht) (a.F_degree t ht) i j]
  apply Finset.sum_congr rfl
  intro k _
  have hc : wordValue 3 t (modelTable t a M cache i j k) =
      RingBasis.structureConstant (a.F t) i j k := by
    change (RingProgram.scalarRing 3 t M cache).decode
      ((RingProgram.structureTableRun (RingProgram.scalarRing 3 t M cache).program
        (RingProgram.liftCoefficientsRun t a.coefficients).1).1 i j k) = _
    rw [RingProgram.structureTableRun_remainder (RingProgram.scalarRing 3 t M cache) hd]
    change (Polynomial.X ^ (i.val+j.val) %ₘ RingProgram.quotientPolynomial
      (RingProgram.scalarRing 3 t M cache) (RingProgram.liftCoefficientsRun t a.coefficients).1).coeff k = _
    rw [RingProgram.modelPolynomial t ht a M cache]
    all_goals rfl
  rw [hc]

theorem model_row_denote (t : ℕ) (ht : 0 < t) [NeZero (3^t)] {n d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (vars : Finset (Fin n)) (u J : ℕ)
    (minusOne : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one : List (Product.Entry n (baseWidth 3 t) d))
    (incidence : Fin n → List (Product.Entry n (baseWidth 3 t) d))
    (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (honeval : rawDenote (RingProgram.modelRing t ht hd a M cache).decode one = Squarefree.canonical u J 1)
    (jet : Fin n → Squarefree.Jet (Fin n) (a.O t))
    (ws : List (Row.WeightedClause n (baseWidth 3 t) d))
    (hjet : ∀ w ∈ ws, ∀ l ∈ w.literals,
      rawDenote (RingProgram.modelRing t ht hd a M cache).decode (incidence l.variable) =
        Squarefree.canonical u J (jet l.variable)) :
    letI : CommRing (Squarefree.Poly (Fin n) (a.O t)) := inferInstance
    letI : CommRing (Squarefree.ZJet (Fin n) (a.O t)) := inferInstance
    letI : CommRing (Squarefree.Jet (Fin n) (a.O t)) := inferInstance
    rawDenote (RingProgram.modelRing t ht hd a M cache).decode
      (DynamicFold.value (Row.value 3 t M cache (modelTable t a M cache)
        minusOne one incidence u J) ws []) =
      Squarefree.canonical u J (@MvPolynomial.eval
        (Squarefree.Jet (Fin n) (a.O t)) (Fin n) Polynomial.commSemiring jet
        (rowPolynomial (scalarJet (V := Fin n))
          (sourceTerms (RingProgram.modelRing t ht hd a M cache).decode ws))) := by
  exact row_denote_scoped 3 t M cache (SubexponentialSAT.LiftRing.of (a.F t)) (RingBasis.basis (a.F t))
    (modelTable t a M cache) (model_table_correct t ht hd a M cache) vars u J
    minusOne one incidence hone hi hminus honeval jet ws hjet

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

variable {R : Type*} [CommRing R]
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (htable : ∀ i j, basis i * basis j =
  ∑ k, scalar (wordValue p t (table i j k)) * basis k)
local notation "f" => RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis

include htable in
 theorem branch_row_denote (vars : Finset (Fin n)) (u J : ℕ)
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (one : List (Product.Entry n (baseWidth p t) d))
    (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
    (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))
    (hminus : f minusOne = -1) (honeval : rawDenote f one = Squarefree.canonical u J 1)
    (H : Finset (Fin n)) (a : H → Bool)
    (low : ResidualEmbedding.Free H → Squarefree.Jet (ResidualEmbedding.Free H) R)
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (hjet : ∀ w ∈ ws, ∀ l ∈ w.literals, rawDenote f (incidence l.variable) =
      Squarefree.canonical u J (ResidualEmbedding.ambientValue H a low l.variable)) :
    rawDenote f (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws []) =
      ResidualEmbedding.jet (ResidualEmbedding.inclusion H)
        (Squarefree.canonical u J (MvPolynomial.eval (ResidualEmbedding.residualValue H a low)
          (rowPolynomial (scalarJet (V := ResidualEmbedding.Free H)) (sourceTerms f ws)))) := by
  rw [row_fold_denote_scoped p t M cache scalar basis table htable vars u J minusOne one incidence
    hone hi hminus honeval (ResidualEmbedding.ambientValue H a low) ws hjet [] Good.nil]
  exact ResidualEmbedding.branch_rowFold_source H a low u J (sourceTerms f ws)

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics

end OAI.Algorithms
