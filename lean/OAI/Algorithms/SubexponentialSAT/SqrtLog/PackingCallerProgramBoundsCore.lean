import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBoundsSelection

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

def produceEnvelope (S : ℕ) :=
  4000*(3*S+1)^3+1+(7*planEnvelope S+5)+
    (4+100*(2400*(S+1)^2*(24*(2*S)+34)+11+(16*(2*S)+24)*S))
def prepareEnvelope (S : ℕ) :=
  7*S+6+32*(S+1)*(S+1)+1+4+
    7*(planEnvelope S+(2*S)*S^2+S^2+alphabetEnvelope S)+20
def suffixEnvelope (S : ℕ) := prepareEnvelope S+81000000*sourceEnvelope S^12+
  (7*(34*sourceEnvelope S^4)+5)+48*(2*(34*sourceEnvelope S^4)+3)
def coreEnvelope (S : ℕ) :=
  produceEnvelope S+loaderEnvelope S+selectionEnvelope S+suffixEnvelope S

theorem produce_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    produceBudget p.scopes p.n p.mask ≤ produceEnvelope S := by
  have hb := Cost.native_cubic p.scopes p.n p.mask
  have hp := plans_le h a tail
  have hi := Finished.pair_budget_le p.scopes p.n p.mask p.mask_le
  change _ ≤ 100*(2400*(p.incidences+1)^2*(24*(p.n+p.factors)+34)+11+
    (16*(p.n+p.factors)+24)*p.incidences) at hi
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have hinput : Cost.inputSize p.scopes p.n p.mask ≤ 3*S+1 := by
    have := h.scopes; have := h.n; have := h.mask
    dsimp [Cost.inputSize]; omega
  unfold produceBudget produceEnvelope
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.add_le_add_right (hb.trans (by gcongr)) 1
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left 7 hp) 5
  · apply Nat.add_le_add_left
    exact hi.trans (by gcongr <;> exact h.incidences)

theorem prepare_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (hp : Parameters outside p) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    prepareBudget (selectedStore outside p a tail) ≤ prepareEnvelope S := by
  have hplan := plans_le h a tail
  have ha := alphabet_bytes_le h
  have hw := width_le h
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have h58 : selectedStore outside p a tail 58=outside 58 := by
    simp [selectedStore,cached,loadedStore,planStore]
  have h61 : selectedStore outside p a tail 61=planBits p.scopes p.n p.mask := by
    simp [selectedStore,cached,loadedStore,planStore]
  have h62 : selectedStore outside p a tail 62=((p.words a tail).map ReadPlan.encodeWord).flatten := by
    simp [selectedStore]
  have h53 : selectedStore outside p a tail 53=List.replicate (p.Q*p.r) true := by
    simp [selectedStore,cached]
  have h54 : selectedStore outside p a tail 54=ProgramEncoding.encodeRecords
      (AssignmentAlphabetSemantics.wordBytes p.r p.Q) := by
    simp [selectedStore,cached]
  unfold prepareBudget
  rw [h58,h61,h62,h53,h54,LeafParametersProgram.Serialization.unaryCopyBound_eq,
    hp.incidence,words_bits,List.length_replicate]
  unfold prepareEnvelope
  gcongr <;> first | exact h.incidences | exact h.l58 | decide

theorem suffix_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (hp : Parameters outside p) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    suffixBudget (selectedStore outside p a tail) (p.spec a tail) ≤ suffixEnvelope S := by
  have hs := source_le h a tail
  have hb := (NativePackingBounds.budget_le (p.spec a tail)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 12))
  have hm := (NativePackingBounds.metadata_output_bytes_le (p.spec a tail)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4))
  have hc := clearLowBudget_le ((p.spec a tail).suffix.outputState (fun _=>false))
    (34*sourceEnvelope S^4) (fun i => (NativePackingBounds.output_word_le (p.spec a tail)
      (fun _=>false) i).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4)))
  have hp := prepare_le h hp a tail
  unfold suffixBudget suffixEnvelope
  omega

theorem coreBudget_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (hp : Parameters outside p) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q) :
    coreBudget outside p a tail ≤ coreEnvelope S := by
  have h0 := produce_le h a tail
  have h1 := loader_le h hp
  have h2 := selection_le h a tail hrows
  have h3 := suffix_le h hp a tail
  unfold coreBudget coreEnvelope
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
