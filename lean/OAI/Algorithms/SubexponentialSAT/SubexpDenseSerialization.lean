import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPayloadBounds
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# Actual framed dense-value sizes and the literal-push machine

Records contain a framed exponent key followed by a framed coefficient payload.
The outer list uses `Encoding.encodeList`, including its termination bit. Bounds
therefore cover actual Boolean lists, not only counts of abstract coefficient
slots. The final theorem uses the existing concrete postfix-push program and its
primitive compiler. It does not implement the arithmetic services.
-/

namespace SubexponentialSAT.SubexpDenseSerialization

open SymbolicCost SubexpSymbolicCost
open scoped BigOperators

def encodeRecord {D : ℕ} {C : Type*} (encodeCoeff : C → List Bool)
    (a : RawIndex D × C) : List Bool :=
  framedRecord (encodeIndex a.1) (encodeCoeff a.2)

def encodeCoefficients {D : ℕ} {C : Type*} (encodeCoeff : C → List Bool)
    (P : CoeffList D C) : List Bool := Encoding.encodeList (encodeRecord encodeCoeff) P

/-- The uniform key ABI pads short keys and preserves longer raw keys. Only
retained keys have the exact canonical width expected by the dense adder. -/
def encodeFixedRecord {D : ℕ} {C : Type*} (encodeCoeff : C → List Bool)
    (a : RawIndex D × C) : List Bool :=
  framedRecord (fixedKey a.1) (encodeCoeff a.2)

def encodeFixedCoefficients {D : ℕ} {C : Type*} (encodeCoeff : C → List Bool)
    (P : CoeffList D C) : List Bool := Encoding.encodeList (encodeFixedRecord encodeCoeff) P

theorem encodeFixedRecord_injective {D : ℕ} {C : Type*}
    {encodeCoeff : C → List Bool} (hcoeff : Function.Injective encodeCoeff) :
    Function.Injective (encodeFixedRecord (D := D) encodeCoeff) := by
  intro a b h
  have hp : (fixedKey a.1, encodeCoeff a.2) = (fixedKey b.1, encodeCoeff b.2) :=
    framedRecord_injective h
  exact Prod.ext (fixedKey_injective (congrArg Prod.fst hp))
    (hcoeff (congrArg Prod.snd hp))

theorem encodeFixedCoefficients_injective {D : ℕ} {C : Type*}
    {encodeCoeff : C → List Bool} (hcoeff : Function.Injective encodeCoeff) :
    Function.Injective (encodeFixedCoefficients (D := D) encodeCoeff) :=
  Encoding.encodeList_injective (encodeFixedRecord_injective hcoeff)

/-- Exact bit length, including both inner frames and the outer list framing. -/
theorem encodeFixedCoefficients_length {D : ℕ} {C : Type*}
    (encodeCoeff : C → List Bool) (P : CoeffList D C) (W : ℕ)
    (hkey : ∀ a ∈ P, Retained D a.1)
    (hcoeff : ∀ a ∈ P, (encodeCoeff a.2).length = W) :
    (encodeFixedCoefficients encodeCoeff P).length =
      1 + (4 * indexBits D + 4 * W + 6) * P.length := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    have ih' := ih (fun b hb => hkey b (List.mem_cons_of_mem a hb))
      (fun b hb => hcoeff b (List.mem_cons_of_mem a hb))
    change (Encoding.encodeList (encodeFixedRecord encodeCoeff) (a :: P)).length = _
    rw [Encoding.length_encodeList_cons]
    change 2 * (encodeFixedRecord encodeCoeff a).length + 2 +
      (encodeFixedCoefficients encodeCoeff P).length = _
    rw [ih']
    simp only [encodeFixedRecord, framedRecord_length,
      fixedKey_length a.1 (hkey a List.mem_cons_self),
      hcoeff a List.mem_cons_self, List.length_cons]
    ring

theorem fixedKey_length_eq_max {D : ℕ} (a : RawIndex D) :
    (fixedKey a).length = max (indexBits D) (encodeIndex a).length := by
  simp only [fixedKey, List.length_append, List.length_replicate]
  omega

theorem encodeFixedCoefficients_length_le {D : ℕ} {C : Type*}
    (encodeCoeff : C → List Bool) (P : CoeffList D C) (I W : ℕ)
    (hkey : ∀ a ∈ P, (fixedKey a.1).length ≤ I)
    (hcoeff : ∀ a ∈ P, (encodeCoeff a.2).length ≤ W) :
    (encodeFixedCoefficients encodeCoeff P).length ≤
      1 + (4 * I + 4 * W + 6) * P.length := by
  have hr : ∀ a ∈ P, (encodeFixedRecord encodeCoeff a).length ≤ 2 * I + 2 * W + 2 := by
    intro a ha
    have hk := hkey a ha
    have hc := hcoeff a ha
    simp only [encodeFixedRecord, framedRecord_length]
    omega
  have h := Encoding.length_encodeList_upper _ P (2 * I + 2 * W + 2) hr
  have he : 2 * (2 * I + 2 * W + 2) + 2 = 4 * I + 4 * W + 6 := by omega
  simpa only [encodeFixedCoefficients,he] using h

/-- Raw literals can exceed the canonical padding width. This bound uses the
actual nontruncating padded key, without assuming retained exponents. -/
theorem raw_fixed_serialized_length {D : ℕ} {C : Type*}
    (encodeCoeff : C → List Bool) (P : CoeffList D C) (I W : ℕ)
    (hkey : ∀ a ∈ P, (encodeIndex a.1).length ≤ I)
    (hcoeff : ∀ a ∈ P, (encodeCoeff a.2).length ≤ W) :
    (encodeFixedCoefficients encodeCoeff P).length ≤
      1 + (4 * (indexBits D + I) + 4 * W + 6) * P.length := by
  apply encodeFixedCoefficients_length_le _ _ _ _ _ hcoeff
  intro a ha
  rw [fixedKey_length_eq_max]
  exact max_le (Nat.le_add_right _ _) ((hkey a ha).trans (Nat.le_add_left _ _))

theorem encodeRecord_injective {D : ℕ} {C : Type*} {encodeCoeff : C → List Bool}
    (hcoeff : Function.Injective encodeCoeff) :
    Function.Injective (encodeRecord (D := D) encodeCoeff) := by
  intro a b h
  have hp : (encodeIndex a.1, encodeCoeff a.2) = (encodeIndex b.1, encodeCoeff b.2) :=
    framedRecord_injective h
  exact Prod.ext (encodeIndex_injective (congrArg Prod.fst hp))
    (hcoeff (congrArg Prod.snd hp))

theorem encodeCoefficients_injective {D : ℕ} {C : Type*}
    {encodeCoeff : C → List Bool} (hcoeff : Function.Injective encodeCoeff) :
    Function.Injective (encodeCoefficients (D := D) encodeCoeff) :=
  Encoding.encodeList_injective (encodeRecord_injective hcoeff)

/-- Includes both record frames, every outer list marker, and the final bit. -/
theorem encodeCoefficients_length {D : ℕ} {C : Type*}
    (encodeCoeff : C → List Bool) (P : CoeffList D C) :
    (encodeCoefficients encodeCoeff P).length =
      1 + 6 * P.length + 4 * storedBits encodeCoeff P := by
  induction P with
  | nil => simp [encodeCoefficients, storedBits]
  | cons a P ih =>
    change (Encoding.encodeList (encodeRecord encodeCoeff) (a :: P)).length = _
    rw [Encoding.length_encodeList_cons]
    change 2 * (encodeRecord encodeCoeff a).length + 2 +
      (encodeCoefficients encodeCoeff P).length = _
    rw [ih]
    simp only [encodeRecord, framedRecord_length, List.length_cons,
      storedBits, List.map_cons, List.sum_cons]
    ring

theorem encodeCoefficients_length_le {D : ℕ} {C : Type*}
    (encodeCoeff : C → List Bool) (P : CoeffList D C) (I W : ℕ)
    (hkey : ∀ a ∈ P, (encodeIndex a.1).length ≤ I)
    (hcoeff : ∀ a ∈ P, (encodeCoeff a.2).length ≤ W) :
    (encodeCoefficients encodeCoeff P).length ≤ 1 + (4 * I + 4 * W + 6) * P.length := by
  have hrecord : ∀ a ∈ P, (encodeRecord encodeCoeff a).length ≤ 2 * I + 2 * W + 2 := by
    intro a ha
    have hk := hkey a ha
    have hc := hcoeff a ha
    simp only [encodeRecord, framedRecord_length]
    omega
  have h := Encoding.length_encodeList_upper _ P (2 * I + 2 * W + 2) hrecord
  have he : 2 * (2 * I + 2 * W + 2) + 2 = 4 * I + 4 * W + 6 := by omega
  simpa only [encodeCoefficients,he] using h

/-- The generic two-field list ABI adds two field markers and a final list bit.
This identity distinguishes it from the matcher-compatible pair of frames. -/
theorem twoFieldList_eq (key payload : List Bool) :
    Encoding.encodeList id [key, payload] =
      true :: (Encoding.frame key ++ true :: (Encoding.frame payload ++ [false])) := rfl

theorem twoFieldList_length (key payload : List Bool) :
    (Encoding.encodeList id [key, payload]).length =
      (framedRecord key payload).length + 3 := by
  simp only [twoFieldList_eq, List.length_cons, List.length_append,
    Encoding.length_frame, List.length_nil, framedRecord_length]
  omega

theorem unaryWords_length_exact (ns : List ℕ) :
    (unaryWords ns).length = ns.sum + ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    change (unaryWord n ++ unaryWords ns).length = (n :: ns).sum + (n :: ns).length
    rw [List.length_append, ih]
    simp only [unaryWord, List.length_append, List.length_replicate,
      List.length_nil, List.sum_cons, List.length_cons]
    omega

/-- Exact length of an arbitrary raw key, with no retained-cutoff assumption. -/
theorem encodeIndex_length_exact {D : ℕ} (a : RawIndex D) :
    (encodeIndex a).length = (∑ i, a.1 i) + a.2.1 + a.2.2 + D + 2 := by
  rw [encodeIndex, unaryWords_length_exact]
  simp only [indexData, List.sum_append, List.sum_cons, List.sum_nil, add_zero,
    Fin.sum_ofFn, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  omega

theorem retained_index_linear {D : ℕ} (a : RawIndex D) (ha : Retained D a) :
    (encodeIndex a).length ≤ 5 * D + 2 := by
  rw [encodeIndex_length_exact]
  rcases ha with ⟨hx, hu, hz⟩
  omega

theorem constantIndex_length (D u z : ℕ) :
    (encodeIndex (SubexpArgumentCode.constantIndex D u z)).length = D + u + z + 2 := by
  simp only [encodeIndex_length_exact, SubexpArgumentCode.constantIndex, Finset.sum_const_zero]
  omega

theorem coordinateIndex_length {D : ℕ} (i : Fin D) (u z : ℕ) :
    (encodeIndex (SubexpArgumentCode.coordinateIndex i u z)).length = D + u + z + 3 := by
  simp [encodeIndex_length_exact, SubexpArgumentCode.coordinateIndex]
  omega

theorem rawRow_key_length {D : ℕ} {A : Type*} (u z : ℕ) (a : Fin D → A)
    (entry : RawIndex D × A) (h : entry ∈ SubexpArgumentCode.rawRow u z a) :
    (encodeIndex entry.1).length = D + u + z + 3 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  exact coordinateIndex_length i u z

/-- Raw Taylor literals need not be retained: their pre-projection key bound
depends on the actual row degree `q`. -/
theorem compileArgument_keys {D q : ℕ} {A : Type*} [Neg A]
    (β : A) (a : Fin (q + 1) → Fin D → A) :
    ∀ entry ∈ SubexpArgumentCode.compileArgument β a,
      (encodeIndex entry.1).length ≤ D + q + 4 := by
  intro entry hentry
  simp only [SubexpArgumentCode.compileArgument, List.mem_append] at hentry
  rcases hentry with (hhead | hrow) | htail
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
    rcases hhead with rfl | rfl <;> simp only [constantIndex_length] <;> omega
  · have h := rawRow_key_length 1 0 (a 0) entry hrow
    omega
  · obtain ⟨row, hrow, hentry⟩ := List.mem_flatten.mp htail
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
    have h := rawRow_key_length 0 (j.val + 1) (a j.succ) entry hentry
    have hj := j.isLt
    omega

theorem compileArgument_serialized_length {D q : ℕ} {A : Type*} [Neg A]
    (encodeCoeff : A → List Bool) (W : ℕ) (hW : ∀ c, (encodeCoeff c).length ≤ W)
    (β : A) (a : Fin (q + 1) → Fin D → A) :
    (encodeCoefficients encodeCoeff (SubexpArgumentCode.compileArgument β a)).length ≤
      1 + (4 * (D + q + 4) + 4 * W + 6) * (2 + (q + 1) * D) := by
  simpa only [SubexpArgumentCode.length_compileArgument] using
    encodeCoefficients_length_le encodeCoeff (SubexpArgumentCode.compileArgument β a)
      (D + q + 4) W (compileArgument_keys β a) (fun entry _ => hW entry.2)

theorem compileArgument_fixed_serialized_length {D q : ℕ} {A : Type*} [Neg A]
    (encodeCoeff : A → List Bool) (W : ℕ) (hW : ∀ c, (encodeCoeff c).length ≤ W)
    (β : A) (a : Fin (q + 1) → Fin D → A) :
    (encodeFixedCoefficients encodeCoeff (SubexpArgumentCode.compileArgument β a)).length ≤
      1 + (4 * (indexBits D + (D + q + 4)) + 4 * W + 6) * (2 + (q + 1) * D) := by
  simpa only [SubexpArgumentCode.length_compileArgument] using
    raw_fixed_serialized_length encodeCoeff (SubexpArgumentCode.compileArgument β a)
      (D + q + 4) W (compileArgument_keys β a) (fun entry _ => hW entry.2)

def KeyBound {D : ℕ} {A : Type*} (I : ℕ) (raw : CoeffList D A) : Prop :=
  ∀ entry ∈ raw, (encodeIndex entry.1).length ≤ I

theorem rawScalar_keys {D q : ℕ} {A : Type*} (a : A) :
    KeyBound (D + q + 4) (SubexpWeightCode.rawScalar D a) := by
  intro entry hentry
  simp only [SubexpWeightCode.rawScalar, List.mem_singleton] at hentry
  subst entry
  have h := constantIndex_length D 0 0
  change (encodeIndex (SubexpArgumentCode.constantIndex D 0 0)).length ≤ _
  omega

section GeneratedKeys

open SubexpProgramBuilder SubexpPayloadBounds SubexpExecution

variable {D p q r : ℕ} {K A F : Type*}

theorem factorExpr_keys [Semiring K] [Ring A]
    (lift : K → A) (cache : List (List A))
    (f : FactorData D p q r K A) (x : Fin D → K) :
    EveryLiteral (KeyBound (D + q + 4)) (factorExpr lift cache f x) := by
  let : Zero (Raw D A) := ⟨[]⟩
  let : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  apply everyLiteral_tableExpr
  · intro entry hentry
    change entry ∈ ([] : CoeffList D A) at hentry
    exact (List.not_mem_nil hentry).elim
  · exact rawScalar_keys (1 : A)
  · exact fun a => rawScalar_keys a
  · intro i
    exact compileArgument_keys _ _

theorem groupExpr_keys [Semiring K] [Ring A]
    (lift : K → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A)) (g : Fin r) (x : Fin D → K) :
    EveryLiteral (KeyBound (D + q + 4)) (groupExpr lift cache factors g x) := by
  let : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  apply everyLiteral_product
  · exact rawScalar_keys (1 : A)
  · intro e he
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
    exact factorExpr_keys lift cache f x

theorem block_keys [Add F] [Semiring K] [Ring A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (base : Fin D → F) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    BlockLiterals (KeyBound (D + q + 4))
      (block embed betaLift weightLift cache factors supports outside base increments a) := by
  constructor
  · exact rawScalar_keys _
  · intro terms hterms term hterm
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hterms
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hterm
    exact ⟨rawScalar_keys _, groupExpr_keys betaLift cache factors g _⟩

theorem blocks_keys [Add F] [Semiring K] [Ring A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    EveryLiteral (KeyBound (D + q + 4))
      (SubexpAlgorithm.rawMomentExpression
        (blocks embed betaLift weightLift cache factors supports outside bases increments a)) := by
  let : Zero (Raw D A) := ⟨[]⟩
  let : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  apply everyLiteral_momentExpression
  · intro entry hentry
    change entry ∈ ([] : CoeffList D A) at hentry
    exact (List.not_mem_nil hentry).elim
  · exact rawScalar_keys (1 : A)
  · intro b hb
    obtain ⟨base, _, rfl⟩ := List.mem_map.mp hb
    exact block_keys embed betaLift weightLift cache factors supports outside base increments a

theorem everyLiteral_combine {L : Type*} {P Q S : L → Prop}
    (h : ∀ x, P x → Q x → S x) (e : Algorithm.Expr L)
    (hP : EveryLiteral P e) (hQ : EveryLiteral Q e) : EveryLiteral S e := by
  induction e with
  | lit x => exact h x hP hQ
  | add e f he hf => exact ⟨he hP.1 hQ.1, hf hP.2 hQ.2⟩
  | mul e f he hf => exact ⟨he hP.1 hQ.1, hf hP.2 hQ.2⟩

/-- Entry count and raw-key bounds are both discharged for the generated
moment expression; only the coefficient representation's width is supplied. -/
theorem blocks_serialized_payloads [Add F] [Semiring K] [Ring A]
    (encodeCoeff : A → List Bool) (W : ℕ) (hW : ∀ c, (encodeCoeff c).length ≤ W)
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    EveryLiteral (fun raw => (encodeCoefficients encodeCoeff raw).length ≤
      1 + (4 * (D + q + 4) + 4 * W + 6) * (2 + (q + 1) * D))
      (SubexpAlgorithm.rawMomentExpression
        (blocks embed betaLift weightLift cache factors supports outside bases increments a)) := by
  apply everyLiteral_combine _ _
    (SubexpPayloadBounds.blocks_everyLiteral embed betaLift weightLift cache factors
      supports outside bases increments a)
    (blocks_keys embed betaLift weightLift cache factors supports outside bases increments a)
  intro raw hlen hkey
  exact (encodeCoefficients_length_le encodeCoeff raw (D + q + 4) W hkey
    (fun entry _ => hW entry.2)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) 1)

theorem blocks_fixed_serialized_payloads [Add F] [Semiring K] [Ring A]
    (encodeCoeff : A → List Bool) (W : ℕ) (hW : ∀ c, (encodeCoeff c).length ≤ W)
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    EveryLiteral (fun raw => (encodeFixedCoefficients encodeCoeff raw).length ≤
      1 + (4 * (indexBits D + (D + q + 4)) + 4 * W + 6) * (2 + (q + 1) * D))
      (SubexpAlgorithm.rawMomentExpression
        (blocks embed betaLift weightLift cache factors supports outside bases increments a)) := by
  apply everyLiteral_combine _ _
    (SubexpPayloadBounds.blocks_everyLiteral embed betaLift weightLift cache factors
      supports outside bases increments a)
    (blocks_keys embed betaLift weightLift cache factors supports outside bases increments a)
  intro raw hlen hkey
  exact (raw_fixed_serialized_length encodeCoeff raw (D + q + 4) W hkey
    (fun entry _ => hW entry.2)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) 1)

end GeneratedKeys

theorem programProject_keys {D : ℕ} {C : Type*} (ops : RingProgram C)
    (slots : List (RawIndex D)) (P : CoeffList D C) :
    ((programProject ops slots P).1.map Prod.fst) = slots := by
  induction slots with
  | nil => rfl
  | cons a slots ih => simpa only [programProject, List.map_cons] using congrArg (List.cons a) ih

theorem programEval_keys {D : ℕ} {C : Type*} (ops : RingProgram C)
    (slots : List (RawIndex D)) (e : Algorithm.Expr (CoeffList D C)) :
    ((SubexpExecution.programEval ops slots e).1.map Prod.fst) = slots := by
  cases e with
  | lit P => exact programProject_keys ops slots P
  | add e f => exact programProject_keys ops slots _
  | mul e f => exact programProject_keys ops slots _

theorem programEval_retained {D : ℕ} {C : Type*} (ops : RingProgram C)
    (slots : List (RawIndex D)) (hs : ∀ a ∈ slots, Retained D a)
    (e : Algorithm.Expr (CoeffList D C)) :
    ∀ a ∈ (SubexpExecution.programEval ops slots e).1, Retained D a.1 := by
  intro a ha
  have hm : a.1 ∈ ((SubexpExecution.programEval ops slots e).1.map Prod.fst) :=
    List.mem_map_of_mem ha
  rw [programEval_keys] at hm
  exact hs a.1 hm

theorem programEval_fixed_serialized_length {D : ℕ} {C : Type*}
    (ops : RingProgram C) (encodeCoeff : C → List Bool) (W : ℕ)
    (hW : ∀ c, (encodeCoeff c).length = W)
    (slots : List (RawIndex D)) (hs : ∀ a ∈ slots, Retained D a)
    (e : Algorithm.Expr (CoeffList D C)) :
    (encodeFixedCoefficients encodeCoeff (SubexpExecution.programEval ops slots e).1).length =
      1 + (4 * indexBits D + 4 * W + 6) * slots.length := by
  simpa only [SubexpExecution.programEval_length] using
    encodeFixedCoefficients_length encodeCoeff (SubexpExecution.programEval ops slots e).1 W
      (programEval_retained ops slots hs e) (fun a _ => hW a.2)

/-- Every intermediate evaluator result has bounded serialized size; no
canonical-value assumption on the raw coefficient words is required. -/
theorem programEval_serialized_length {D : ℕ} {C : Type*}
    (ops : RingProgram C) (encodeCoeff : C → List Bool) (W : ℕ)
    (hW : ∀ c, (encodeCoeff c).length ≤ W)
    (slots : List (RawIndex D)) (hs : ∀ a ∈ slots, Retained D a)
    (e : Algorithm.Expr (CoeffList D C)) :
    (encodeCoefficients encodeCoeff (SubexpExecution.programEval ops slots e).1).length ≤
      1 + (4 * indexBits D + 4 * W + 6) * slots.length := by
  have hkey : ∀ a ∈ (SubexpExecution.programEval ops slots e).1,
      (encodeIndex a.1).length ≤ indexBits D := by
    intro a ha
    have hm : a.1 ∈ ((SubexpExecution.programEval ops slots e).1.map Prod.fst) :=
      List.mem_map_of_mem ha
    rw [programEval_keys] at hm
    exact retained_index_bits a.1 (hs a.1 hm)
  simpa only [SubexpExecution.programEval_length] using
    encodeCoefficients_length_le encodeCoeff (SubexpExecution.programEval ops slots e).1
      (indexBits D) W hkey (fun a _ => hW a.2)

/-- Actual four-word payloads; no semantic quotient-ring encoding is used. -/
def encodeQuarticCoefficients (p D : ℕ) : CoeffList D (QuarticCode p D) → List Bool :=
  encodeCoefficients (quarticCodeBlockCode p D).block

theorem encodeQuarticCoefficients_injective (p D : ℕ) :
    Function.Injective (encodeQuarticCoefficients p D) :=
  encodeCoefficients_injective (quarticCodeBlockCode p D).injective_block

def encodeFixedQuarticCoefficients (p D : ℕ) : CoeffList D (QuarticCode p D) → List Bool :=
  encodeFixedCoefficients (quarticCodeBlockCode p D).block

theorem encodeFixedQuarticCoefficients_injective (p D : ℕ) :
    Function.Injective (encodeFixedQuarticCoefficients p D) :=
  encodeFixedCoefficients_injective (quarticCodeBlockCode p D).injective_block

theorem quartic_programEval_fixed_serialized_length (p D : ℕ)
    (ops : RingProgram (QuarticCode p D)) (slots : List (RawIndex D))
    (hs : ∀ a ∈ slots, Retained D a)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) :
    (encodeFixedQuarticCoefficients p D (SubexpExecution.programEval ops slots e).1).length =
      1 + (4 * indexBits D + 4 * coefficientBits D 4 (Nat.log 2 p + 1) + 6) *
        slots.length := by
  apply programEval_fixed_serialized_length _ _ _ _ slots hs e
  intro c
  rw [(quarticCodeBlockCode p D).length_block, quarticCodeBlockCode_width]

theorem quartic_raw_serialized_length (p D : ℕ)
    (P : CoeffList D (QuarticCode p D)) (I : ℕ)
    (hkey : ∀ a ∈ P, (encodeIndex a.1).length ≤ I) :
    (encodeQuarticCoefficients p D P).length ≤
      1 + (4 * I + 4 * coefficientBits D 4 (Nat.log 2 p + 1) + 6) * P.length := by
  apply encodeCoefficients_length_le _ _ _ _ hkey
  intro a _
  rw [(quarticCodeBlockCode p D).length_block, quarticCodeBlockCode_width]

theorem quartic_programEval_serialized_length (p D : ℕ)
    (ops : RingProgram (QuarticCode p D)) (slots : List (RawIndex D))
    (hs : ∀ a ∈ slots, Retained D a)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) :
    (encodeQuarticCoefficients p D (SubexpExecution.programEval ops slots e).1).length ≤
      1 + (4 * indexBits D + 4 * coefficientBits D 4 (Nat.log 2 p + 1) + 6) *
        slots.length := by
  apply programEval_serialized_length _ _ _ _ slots hs e
  intro c
  rw [(quarticCodeBlockCode p D).length_block, quarticCodeBlockCode_width]

/-- The complete framing cost is still a fixed polynomial per retained slot. -/
theorem framedSlotBits_degree (D h b : ℕ) :
    4 * indexBits D + 4 * coefficientBits D h b + 6 ≤
      18 * parameterSize D h b ^ 3 := by
  have hi := indexBits_degree D h b
  have hc := coefficientBits_degree D h b
  have hS : 1 ≤ parameterSize D h b := by unfold parameterSize; omega
  have hp : parameterSize D h b ^ 2 ≤ parameterSize D h b ^ 3 :=
    Nat.pow_le_pow_right hS (by decide)
  have hpos : 1 ≤ parameterSize D h b ^ 3 := Nat.one_le_pow _ _ hS
  omega

theorem quartic_dense_serialized_degree (p D : ℕ)
    (ops : RingProgram (QuarticCode p D)) (slots : List (RawIndex D))
    (hs : ∀ a ∈ slots, Retained D a) (hlen : slots.length = slotCount D)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) :
    (encodeQuarticCoefficients p D (SubexpExecution.programEval ops slots e).1).length ≤
      1 + 18 * monomialCount D * parameterSize D 4 (Nat.log 2 p + 1) ^ 5 := by
  apply (quartic_programEval_serialized_length p D ops slots hs e).trans
  rw [hlen, slotCount]
  have hslot := framedSlotBits_degree D 4 (Nat.log 2 p + 1)
  have hD : D + 1 ≤ parameterSize D 4 (Nat.log 2 p + 1) := by unfold parameterSize; omega
  have hp : (D + 1) * D ≤ parameterSize D 4 (Nat.log 2 p + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hD ((Nat.le_succ D).trans hD)
  apply Nat.add_le_add_left
  calc
    _ ≤ (18 * parameterSize D 4 (Nat.log 2 p + 1) ^ 3) *
        (monomialCount D * parameterSize D 4 (Nat.log 2 p + 1) ^ 2) :=
      Nat.mul_le_mul hslot (Nat.mul_le_mul_left _ hp)
    _ = _ := by ring

theorem quartic_fixed_dense_serialized_degree (p D : ℕ)
    (ops : RingProgram (QuarticCode p D)) (slots : List (RawIndex D))
    (hs : ∀ a ∈ slots, Retained D a) (hlen : slots.length = slotCount D)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) :
    (encodeFixedQuarticCoefficients p D (SubexpExecution.programEval ops slots e).1).length ≤
      1 + 18 * monomialCount D * parameterSize D 4 (Nat.log 2 p + 1) ^ 5 := by
  rw [quartic_programEval_fixed_serialized_length p D ops slots hs e, hlen, slotCount]
  have hslot := framedSlotBits_degree D 4 (Nat.log 2 p + 1)
  have hD : D + 1 ≤ parameterSize D 4 (Nat.log 2 p + 1) := by unfold parameterSize; omega
  have hp : (D + 1) * D ≤ parameterSize D 4 (Nat.log 2 p + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hD ((Nat.le_succ D).trans hD)
  apply Nat.add_le_add_left
  calc
    _ ≤ (18 * parameterSize D 4 (Nat.log 2 p + 1) ^ 3) *
        (monomialCount D * parameterSize D 4 (Nat.log 2 p + 1) ^ 2) :=
      Nat.mul_le_mul hslot (Nat.mul_le_mul_left _ hp)
    _ = _ := by ring

def encodeQuarticList (p D : ℕ) : List (QuarticCode p D) → List Bool :=
  Encoding.encodeList (quarticCodeBlockCode p D).block

theorem encodeQuarticList_injective (p D : ℕ) :
    Function.Injective (encodeQuarticList p D) :=
  Encoding.encodeList_injective (quarticCodeBlockCode p D).injective_block

/-- Univariate interpolation lists have one frame per coefficient. -/
theorem encodeQuarticList_length (p D : ℕ) (P : List (QuarticCode p D)) :
    (encodeQuarticList p D P).length =
      1 + (2 * coefficientBits D 4 (Nat.log 2 p + 1) + 2) * P.length := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    change (Encoding.encodeList (quarticCodeBlockCode p D).block (a :: P)).length = _
    rw [Encoding.length_encodeList_cons, (quarticCodeBlockCode p D).length_block,
      quarticCodeBlockCode_width]
    change _ + (encodeQuarticList p D P).length = _
    rw [ih, List.length_cons]
    ring

section Univariate

variable {R : Type*} [CommRing R] (p D : ℕ)
    (ops : RepresentedRing (QuarticCode p D) R)

theorem univariate_mul_serialized_length (P Q : List (QuarticCode p D)) :
    (encodeQuarticList p D (SubexpDensePolynomial.mulRun ops P Q).1).length ≤
      1 + (2 * coefficientBits D 4 (Nat.log 2 p + 1) + 2) * (P.length + Q.length) := by
  rw [encodeQuarticList_length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _
    (SubexpDensePolynomial.mulRun_length ops P Q)) 1

theorem univariate_shift_serialized_length (a : QuarticCode p D)
    (P : List (QuarticCode p D)) :
    (encodeQuarticList p D (SubexpDensePolynomial.shiftRun ops a P).1).length ≤
      1 + (2 * coefficientBits D 4 (Nat.log 2 p + 1) + 2) * (2 * P.length) := by
  rw [encodeQuarticList_length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _
    (SubexpDensePolynomial.shiftRun_length ops a P)) 1

theorem univariate_sum_serialized_length (Ps : List (List (QuarticCode p D)))
    (L : ℕ) (hL : ∀ P ∈ Ps, P.length ≤ L) :
    (encodeQuarticList p D (SubexpDensePolynomial.sumRun ops Ps).1).length ≤
      1 + (2 * coefficientBits D 4 (Nat.log 2 p + 1) + 2) * L := by
  rw [encodeQuarticList_length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _
    (SubexpDensePolynomial.sumRun_length ops Ps L hL)) 1

theorem univariate_product_serialized_length (Ps : List (List (QuarticCode p D)))
    (L : ℕ) (hL : ∀ P ∈ Ps, P.length ≤ L) :
    (encodeQuarticList p D (SubexpDensePolynomial.productRun ops Ps).1).length ≤
      1 + (2 * coefficientBits D 4 (Nat.log 2 p + 1) + 2) * (1 + Ps.length * L) := by
  rw [encodeQuarticList_length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _
    (SubexpDensePolynomial.productRun_length ops Ps L hL)) 1

end Univariate

/-- A serialization-size bound yields a runtime bound for the actual compiled
push program, for any payload ABI. -/
theorem encoded_push_primitive {C : Type*} (encode : C → List Bool)
    (x : C) (B : ℕ) (hB : (encode x).length ≤ B)
    (is : List (Algorithm.Instr C)) (xs : List C) (v present op : Bool) :
    Computation.RunsIn (BitProgram.primitive SubexpPostfixControl.pushLoopProgram).step
      (BitProgram.primitiveOverhead SubexpPostfixControl.pushLoopProgram * (11 * B + 17))
      (BitProgram.primitiveCfg SubexpPostfixControl.pushLoopProgram
        (SubexpPostfixControl.cfg4 (some 0) v present op
          (SubexpPostfixControl.serializeCode encode (.push x :: is))
          (SubexpPostfixControl.operandDepth xs) (Encoding.encodeList encode xs) []))
      (BitProgram.primitiveCfg SubexpPostfixControl.pushLoopProgram
        (SubexpPostfixControl.cfg4 (some 0) true false op
          (SubexpPostfixControl.serializeCode encode is)
          (SubexpPostfixControl.operandDepth (x :: xs))
          (Encoding.encodeList encode (x :: xs)) [])) := by
  obtain ⟨steps, hsteps, htrace⟩ :=
    BitProgram.primitive_trace SubexpPostfixControl.pushLoopProgram
      (SubexpPostfixControl.serialized_push_complete_trace encode x is xs v present op)
  refine ⟨steps, hsteps.trans ?_, htrace⟩
  exact Nat.mul_le_mul_left _ (by omega)

/-- A concrete finite-control push, after compiling to primitive tape steps.
The linear bound depends on the actual framed literal length established above. -/
theorem literal_push_primitive {D : ℕ} {C : Type*}
    (encodeCoeff : C → List Bool) (P : CoeffList D C) (I W : ℕ)
    (hkey : ∀ a ∈ P, (encodeIndex a.1).length ≤ I)
    (hcoeff : ∀ a ∈ P, (encodeCoeff a.2).length ≤ W)
    (is : List (Algorithm.Instr (CoeffList D C))) (xs : List (CoeffList D C))
    (v present op : Bool) :
    Computation.RunsIn (BitProgram.primitive SubexpPostfixControl.pushLoopProgram).step
      (BitProgram.primitiveOverhead SubexpPostfixControl.pushLoopProgram *
        (11 * (1 + (4 * I + 4 * W + 6) * P.length) + 17))
      (BitProgram.primitiveCfg SubexpPostfixControl.pushLoopProgram
        (SubexpPostfixControl.cfg4 (some 0) v present op
          (SubexpPostfixControl.serializeCode (encodeCoefficients encodeCoeff) (.push P :: is))
          (SubexpPostfixControl.operandDepth xs)
          (Encoding.encodeList (encodeCoefficients encodeCoeff) xs) []))
      (BitProgram.primitiveCfg SubexpPostfixControl.pushLoopProgram
        (SubexpPostfixControl.cfg4 (some 0) true false op
          (SubexpPostfixControl.serializeCode (encodeCoefficients encodeCoeff) is)
          (SubexpPostfixControl.operandDepth (P :: xs))
          (Encoding.encodeList (encodeCoefficients encodeCoeff) (P :: xs)) [])) := by
  have ht := BitProgram.primitive_trace SubexpPostfixControl.pushLoopProgram
    (SubexpPostfixControl.serialized_push_complete_trace
      (encodeCoefficients encodeCoeff) P is xs v present op)
  have hl := encodeCoefficients_length_le encodeCoeff P I W hkey hcoeff
  obtain ⟨steps, hsteps, htrace⟩ := ht
  refine ⟨steps, hsteps.trans ?_, htrace⟩
  exact Nat.mul_le_mul_left _ (by omega)

end SubexponentialSAT.SubexpDenseSerialization

end OAI.Algorithms
