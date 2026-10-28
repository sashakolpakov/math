import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheProduct

namespace OAI.Algorithms

/-! Exact word and accumulator states of the runtime Lagrange loops. -/

namespace SubexponentialSAT.SubexpLagrangeCacheState

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheWorkspace

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Coefficient := Quad (Word (baseWidth p μ))

/-- This is the word recurrence executed by the actual add-one calls. -/
def label (zero one : Coefficient p μ) : ℕ → Coefficient p μ
  | 0 => zero
  | n + 1 => (SubexpPreparedQuartic.binaryAdd p μ M (label zero one n) one).1

theorem label_value (c : Fin 4 → ZMod (p ^ μ)) (zero one : Coefficient p μ)
    (hz : quotientDenote c (zero.map (wordValue p μ)) = 0)
    (ho : quotientDenote c (one.map (wordValue p μ)) = 1) (n : ℕ) :
    quotientDenote c ((label p μ M zero one n).map (wordValue p μ)) =
      (n : LiftRing.Extension (QuarticSearch.poly c)) := by
  induction n with
  | zero => simpa only [label, Nat.cast_zero] using hz
  | succ n ih =>
      rw [label, SubexpPreparedQuartic.binaryAdd_quotient, ih, ho, Nat.cast_add, Nat.cast_one]

structure Partial (D : ℕ) where
  denominator : Coefficient p μ
  polynomial : List (Coefficient p μ)
  length_eq : polynomial.length = D

def advance (D : ℕ) (t zero one : Coefficient p μ) (minusOne : Word (baseWidth p μ))
    (i j : ℕ) (a : Partial p μ D) : Partial p μ D :=
  if i = j then a else
    ⟨SubexpLagrangeCacheProduct.denominator p μ M t minusOne a.denominator
        (label p μ M zero one i) (label p μ M zero one j),
      SubexpLagrangeCacheProduct.polynomial p μ M t zero one minusOne
        (label p μ M zero one j) D a.polynomial,
      SubexpTruncatedMultiply.result_length _ _ _ _ _ _ _ _⟩

def run (D : ℕ) (t zero one : Coefficient p μ) (minusOne : Word (baseWidth p μ))
    (i : ℕ) : ℕ → ℕ → Partial p μ D → Partial p μ D
  | _, 0, a => a
  | j, n + 1, a => run D t zero one minusOne i (j + 1) n
      (advance p μ M D t zero one minusOne i j a)

def encode (xs : List (Coefficient p μ)) : List Bool :=
  SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode xs

def view (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update base
    205 (SubexpFlatAdd.encode a.denominator)) 218 (SubexpFlatAdd.encode (label p μ M zero one j)))
      240 (encode p μ a.polynomial)) 249 (List.replicate j false)) 247 todo

omit [Fact p.Prime] in
theorem view_other (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) (port : Fin 256)
    (h205 : port ≠ 205) (h218 : port ≠ 218) (h240 : port ≠ 240)
    (h249 : port ≠ 249) (h247 : port ≠ 247) :
    view p μ M D base zero one j a todo port = base port := by
  simp only [view, Function.update_of_ne h205, Function.update_of_ne h218,
    Function.update_of_ne h240, Function.update_of_ne h249, Function.update_of_ne h247]

omit [Fact p.Prime] in
theorem view_workspace (D : ℕ) (base : Store) (t zero one : Coefficient p μ)
    (width : List Bool) (H : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) base)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) :
    Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ)
      (view p μ M D base zero one j a todo) := by
  exact ((((H.update 205 (by decide) _).update 218 (by decide) _).update 240
    (by decide) _).update 249 (by decide) _).update 247 (by decide) _

omit [Fact p.Prime] in
theorem view_denominator (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) :
    view p μ M D base zero one j a todo 205 = SubexpFlatAdd.encode a.denominator := by
  simp [view]

omit [Fact p.Prime] in
theorem view_label (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) :
    view p μ M D base zero one j a todo 218 =
      SubexpFlatAdd.encode (label p μ M zero one j) := by simp [view]

omit [Fact p.Prime] in
theorem view_polynomial (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) :
    view p μ M D base zero one j a todo 240 = encode p μ a.polynomial := by simp [view]

omit [Fact p.Prime] in
theorem view_index (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) :
    view p μ M D base zero one j a todo 249 = List.replicate j false := by simp [view]

omit [Fact p.Prime] in
theorem view_counter (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) :
    view p μ M D base zero one j a todo 247 = todo := by simp [view]

omit [Fact p.Prime] in
theorem view_partial (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a b : Partial p μ D) (todo : List Bool) :
    Function.update (Function.update (view p μ M D base zero one j a todo)
      205 (SubexpFlatAdd.encode b.denominator)) 240 (encode p μ b.polynomial) =
      view p μ M D base zero one j b todo := by
  funext k
  by_cases h205 : k = 205
  · subst k; simp [view]
  · by_cases h240 : k = 240
    · subst k; simp [view]
    · simp [view, Function.update_apply, h205, h240]

omit [Fact p.Prime] in
theorem view_next (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (todo : List Bool) :
    Function.update (Function.update (view p μ M D base zero one j a todo)
      218 (SubexpFlatAdd.encode (label p μ M zero one (j + 1)))) 249
        (false :: List.replicate j false) = view p μ M D base zero one (j + 1) a todo := by
  funext k
  by_cases h218 : k = 218
  · subst k; simp [view]
  · by_cases h249 : k = 249
    · subst k; simp [view, List.replicate_succ]
    · simp [view, Function.update_apply, h218, h249]

omit [Fact p.Prime] in
theorem view_todo (D : ℕ) (base : Store) (zero one : Coefficient p μ)
    (j : ℕ) (a : Partial p μ D) (old todo : List Bool) :
    Function.update (view p μ M D base zero one j a old) 247 todo =
      view p μ M D base zero one j a todo := by
  funext k
  by_cases hk : k = 247 <;> simp [view, hk]

end SubexponentialSAT.SubexpLagrangeCacheState

end OAI.Algorithms
