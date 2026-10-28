import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBoundsLoader

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

def scoreEnvelope (S : ℕ) := (S*S)^2*(S^2*S^4)+8*(S*S)^2*((2*S)*S^2)
def controllerEnvelope (S : ℕ) :=
  (2*S)*(PackingProgram.Assembly.uniformBudget (2*S) (S^2) (S^2) S (S^2) S
    (S^2*S^2+8*S^2*S^2) (4*S)+
      SequentialProgram.selectionBudget S (scoreEnvelope S) (2*S) (S^2)+3)+3

def selectionEnvelope (S : ℕ) :=
  7*readyEnvelope S+5+(7*readyEnvelope S+5)+controllerEnvelope S+
    (7*((2*S)*S^2)+5)+48*(2*(48*readyEnvelope S+(2*S)*S^2+2*S+1)+3)

theorem controller_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q) :
    PackingProgram.Assembly.Scope.cost p.scopes p.n p.mask a tail p.s
      (outside 56) (outside 57) (outside 58) (outside 59) ≤ controllerEnvelope S := by
  have ha : (a::tail).length=p.r^p.Q := by
    have hh := congrArg List.length hrows
    simpa only [List.length_map,AssignmentAlphabetSemantics.wordBytes_length] using hh
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have hw := width_le h
  have hparam : (outside 56).length+(outside 57).length+(outside 58).length+(outside 59).length ≤ 4*S := by
    have := h.l56; have := h.l57; have := h.l58; have := h.l59; omega
  unfold PackingProgram.Assembly.Scope.cost PackingProgram.Assembly.controllerCost
  simp only [Packing.headsFirst_length,List.length_finRange]
  change (p.n+p.factors)*(PackingProgram.Assembly.uniformBudget (p.n+p.factors)
    (PackingProgram.Assembly.Scope.pairs p.scopes p.mask).length p.raw.length (a::tail).length
    (p.Q*p.r) p.n (PackingProgram.Assembly.magnitude p.n p.s p.incidences p.r)
    (PackingProgram.Assembly.parameterBits (outside 56) (outside 57) (outside 58) (outside 59))+
    SequentialProgram.selectionBudget (a::tail).length
      (PackingProgram.Assembly.scoreBound (a::tail)
        (PackingProgram.Assembly.Scope.pairs p.scopes p.mask)
        (Packing.headsFirstIndices (List.finRange p.n) (List.finRange p.factors)) p.n p.s p.incidences)
      (p.n+p.factors) (ReadPlan.encodeWord a).length+3)+3 ≤ _
  simp only [ha,raw_length,pairs_length,ReadPlan.encodeWord_length,ReadPlan.wordWidth,
    PackingProgram.Assembly.scoreBound,Packing.headsFirst_length,List.length_finRange]
  unfold controllerEnvelope scoreEnvelope PackingProgram.Assembly.magnitude
    PackingProgram.Assembly.parameterBits PackingProgram.Assembly.uniformBudget
    PackingProgram.Assembly.headBudgetBound SequentialProgram.selectionBudget
    SequentialProgram.minimumBudget SequentialProgram.recordBudget SequentialProgram.updateBudget
  dsimp only
  gcongr <;> first | exact hn | exact hw | exact hparam | exact h.n | exact h.s | exact h.r | exact h.incidences | exact h.alphabet

theorem selection_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q) :
    selectionBudget (ready outside p (fun _=>false)) ((p.words a tail).map ReadPlan.encodeWord)
      (PackingProgram.Assembly.Scope.cost p.scopes p.n p.mask a tail p.s
        (outside 56) (outside 57) (outside 58) (outside 59)) ≤ selectionEnvelope S := by
  have hc := controller_le h a tail hrows
  have h10 := ready_word_le h (fun _=>false) 10
  have h39 := ready_word_le h (fun _=>false) 39
  have hm := ready_mass_le h (fun _=>false)
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have hw := width_le h
  unfold selectionBudget selectionSize selectionEnvelope
  rw [words_bits,List.length_map,p.words_length]
  gcongr

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
