import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBoundsBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

def outputEnvelope (S : ℕ) :=
  S+S^2+alphabetEnvelope S+planEnvelope S+(2*S)*S^2+34*sourceEnvelope S^4

theorem outputStore_word_le {outside : Store} {p : Problem} {S B : ℕ}
    (h : Cap outside p S) (ho : ∀ i,(outside i).length ≤ B)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64) :
    ((outputStore outside p a tail) i).length ≤ B+outputEnvelope S := by
  have hs := source_le h a tail
  have hm := (NativePackingBounds.metadata_output_bytes_le (p.spec a tail)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4))
  have hp := plans_le h a tail
  have ha := alphabet_bytes_le h
  have hw := width_le h
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have hwords : ((p.words a tail).map ReadPlan.encodeWord).flatten.length ≤ (2*S)*S^2 := by
    rw [words_bits]; exact Nat.mul_le_mul hn hw
  have hsc := h.scopes
  have hoi := ho i
  by_cases h63 : i=63
  · subst i; simp only [outputStore,Function.update_same]; unfold outputEnvelope; omega
  by_cases h62 : i=62
  · subst i
    simp only [outputStore,selectedStore,Function.update_of_ne (by decide : (62 : Fin 64)≠63),Function.update_same]
    unfold outputEnvelope; omega
  by_cases h54 : i=54
  · subst i
    simp [outputStore,selectedStore,cached,loadedStore,planStore]
    unfold outputEnvelope; omega
  by_cases h53 : i=53
  · subst i
    simp [outputStore,selectedStore,cached,loadedStore,planStore]
    unfold outputEnvelope; omega
  by_cases h60 : i=60
  · subst i
    simp [outputStore,selectedStore,cached,loadedStore,planStore]
    unfold outputEnvelope; omega
  by_cases h61 : i=61
  · subst i
    simp [outputStore,selectedStore,cached,loadedStore,planStore]
    unfold outputEnvelope; omega
  simp only [outputStore,selectedStore,cached,loadedStore,planStore,
    Function.update_of_ne h63,Function.update_of_ne h62,Function.update_of_ne h54,
    Function.update_of_ne h53,Function.update_of_ne h60,Function.update_of_ne h61]
  omega

theorem parameterStore_word_le (a : Wide.Data) (p : Problem) (i : Fin 64) :
    ((Wide.parameterStore (Wide.project a)) i).length ≤ scalarSize (Wide.parameterStore (Wide.project a)) p := by
  have h := scalarSize_cap (Wide.parameterStore (Wide.project a)) p
  have h55 := h.l55
  have h56 := h.l56
  have h57 := h.l57
  have h58 := h.l58
  have h59 := h.l59
  unfold Wide.parameterStore
  split_ifs <;> subst_vars <;> first | exact h55 | exact h56 | exact h57 | exact h58 | exact h59 | simp

theorem bankOutput_word_le (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64) :
    ((bankOutput a p w tail).stacks i).length ≤
      scalarSize (Wide.parameterStore (Wide.project a)) p+
        outputEnvelope (scalarSize (Wide.parameterStore (Wide.project a)) p) := by
  have h := outputStore_word_le (scalarSize_cap (Wide.parameterStore (Wide.project a)) p)
    (parameterStore_word_le a p) w tail i
  by_cases hi : i.val < 48
  · simp [bankOutput,framed_stack,hi]
  · simpa [bankOutput,framed_stack,hi] using h

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
