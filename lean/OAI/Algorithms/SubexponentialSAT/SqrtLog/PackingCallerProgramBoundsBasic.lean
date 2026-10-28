import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NativePackingBoundsOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyPolynomial

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

/-- Literal input sizes and the two actually generated alphabets. -/
def scalarSize (outside : Store) (p : Problem) : ℕ :=
  p.n+p.factors+p.incidences+p.r+p.Q+p.s+p.r^p.Q+p.r^(2*p.Q)+
  (Scan.scopeBits p.scopes).length+p.mask.length+
  (outside 55).length+(outside 56).length+(outside 57).length+
  (outside 58).length+(outside 59).length+1

structure Cap (outside : Store) (p : Problem) (S : ℕ) : Prop where
  pos : 1 ≤ S
  n : p.n ≤ S
  factors : p.factors ≤ S
  incidences : p.incidences ≤ S
  r : p.r ≤ S
  Q : p.Q ≤ S
  s : p.s ≤ S
  alphabet : p.r^p.Q ≤ S
  types : p.r^(2*p.Q) ≤ S
  scopes : (Scan.scopeBits p.scopes).length ≤ S
  mask : p.mask.length ≤ S
  l55 : (outside 55).length ≤ S
  l56 : (outside 56).length ≤ S
  l57 : (outside 57).length ≤ S
  l58 : (outside 58).length ≤ S
  l59 : (outside 59).length ≤ S

theorem scalarSize_cap (outside : Store) (p : Problem) : Cap outside p (scalarSize outside p) := by
  constructor <;> dsimp [scalarSize] <;> omega

def planEnvelope (S : ℕ) := 1+(16*(2*S)+24)*S
def pairEnvelope (S : ℕ) := 1+(32*(2*S+1)+14)*S^2
def alphabetEnvelope (S : ℕ) := 1+(2*S^2+2)*S
def seedEnvelope (S : ℕ) := 1+(2*(2*S)+2)*(2*S)
def extentEnvelope (S : ℕ) :=
  1+S+S+0+S+S+1+2+S^2+2*S+S+(1+(2*S+2)*S)+
  alphabetEnvelope S+S^2+S*S^2+seedEnvelope S+pairEnvelope S

def sourceEnvelope (S : ℕ) :=
  S+1+S+S^2+(2*S)*S^2+alphabetEnvelope S+planEnvelope S+1

theorem width_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S) :
    p.Q*p.r ≤ S^2 := by simpa [pow_two] using Nat.mul_le_mul h.Q h.r

theorem words_bits (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    ((p.words a tail).map ReadPlan.encodeWord).flatten.length=(p.n+p.factors)*(p.Q*p.r) := by
  rw [ScoreBuilderInputBounds.encodedWords_length,p.words_length]
  rfl

theorem source_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    NativePackingBounds.sourceSize (p.spec a tail) ≤ sourceEnvelope S := by
  have hs := NativePackingBounds.address_sourceSize_le p.hr p.hQ (p.words a tail)
    (Address.address p.scopes p.n p.mask p.mask_le (p.words a tail) (p.words_length a tail))
  rw [p.words_length] at hs
  change NativePackingBounds.sourceSize (p.spec a tail) ≤ _ at hs
  apply hs.trans
  unfold NativePackingBounds.addressSize sourceEnvelope alphabetEnvelope planEnvelope
  have hw := width_le h
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  gcongr <;> first | exact h.incidences | exact h.types | exact hw | exact hn | exact h.alphabet

theorem plans_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (planBits p.scopes p.n p.mask).length ≤ planEnvelope S := by
  have hp := NativePackingBounds.address_plan_stream_le (p.words a tail)
    (Address.address p.scopes p.n p.mask p.mask_le (p.words a tail) (p.words_length a tail))
  change (p.spec a tail).params.planStream.length ≤ _ at hp
  rw [p.spec_plans,p.words_length] at hp
  apply hp.trans
  unfold planEnvelope
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  calc
    _ ≤ 1+(16*(2*S)+24)*S := by gcongr; exact h.incidences
    _ = _ := by ring

theorem pair_bytes_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S) :
    (PairScoreProgram.pairRecords p.raw).length ≤ pairEnvelope S := by
  have hp := Finished.output_bits_le p.scopes p.n p.mask p.mask_le
  change (PairScoreProgram.pairRecords p.raw).length ≤
    1+(32*(p.n+p.factors+1)+14)*p.incidences^2 at hp
  apply hp.trans
  unfold pairEnvelope
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  gcongr ; exact h.incidences

theorem alphabet_bytes_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S) :
    (ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes p.r p.Q)).length ≤
      alphabetEnvelope S := by
  have ha := ProgramEncoding.encodeRecords_length_le (AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (p.Q*p.r) (fun row hm => (AssignmentAlphabetSemantics.wordBytes_width p.hr row hm).le)
  rw [AssignmentAlphabetSemantics.wordBytes_length] at ha
  apply ha.trans
  unfold alphabetEnvelope
  have hw := width_le h
  gcongr ; exact h.alphabet

theorem raw_length (p : Problem) : p.raw.length=p.incidences^2 := by
  simp [Problem.raw,PackingProgram.Assembly.Scope.raw,PackingIncidenceProgram.generatedRawPairs_length,
    Install.plans,Semantics.plans_eq,Semantics.nativeEntries,Problem.incidences,pow_two]

theorem pairs_length (p : Problem) :
    (PackingProgram.Assembly.Scope.pairs p.scopes p.mask).length=p.incidences^2 := by
  unfold PackingProgram.Assembly.Scope.pairs
  have hp := List.length_product (Finished.incidenceList p.scopes p.mask)
    (Finished.incidenceList p.scopes p.mask)
  simpa [SProd.sprod,List.instSProd,Finished.incidenceList,Problem.incidences,pow_two] using hp

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
