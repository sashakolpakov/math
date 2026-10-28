import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramOrdered
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramFinalSize

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage

def inputMass (a : Wide.Data) := ∑ i : Fin 768,(a.stacks i).length

theorem inputMass_bound (a : Wide.Data) (i : Fin 768) : (a.stacks i).length ≤ inputMass a := by
  unfold inputMass
  exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 768 => (a.stacks j).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)

def combinedExponent (dc db : ℕ) := max 1 (max dc db)
def combinedConstant (cc cb : ℕ) := cc+1100*(cb+2)

/-- The global copying, cleanup, and parking add only a linear cost in
the largest input or computed word. This combines independently proved
native-core and output-word polynomial bounds without a runtime oracle. -/
theorem polynomial_envelope (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (V cc dc cb db : ℕ) (hV : 1 ≤ V) (hi : inputMass a ≤ V)
    (hc : coreBudget (Wide.parameterStore (Wide.project a)) p w tail ≤ cc*V^dc)
    (hb : WordBound (cb*V^db) (bankOutput a p w tail)) :
    budget a p w tail ≤ combinedConstant cc cb*V^(combinedExponent dc db) ∧
    WordBound (combinedConstant cc cb*V^(combinedExponent dc db)) (result a p w tail) := by
  let D := combinedExponent dc db
  let N := V^D
  have hd1 : 1 ≤ D := le_max_left _ _
  have hdc : dc ≤ D := (le_max_left dc db).trans (le_max_right _ _)
  have hdb : db ≤ D := (le_max_right dc db).trans (le_max_right _ _)
  have hVN : V ≤ N := by simpa [N] using Nat.pow_le_pow_right hV hd1
  have hN : 1 ≤ N := hV.trans hVN
  have hcN : coreBudget (Wide.parameterStore (Wide.project a)) p w tail ≤ cc*N :=
    hc.trans (Nat.mul_le_mul_left cc (Nat.pow_le_pow_right hV hdc))
  have hbN : WordBound (cb*N) (bankOutput a p w tail) := by
    intro i
    exact (hb i).trans (Nat.mul_le_mul_left cb (Nat.pow_le_pow_right hV hdb))
  have ha : WordBound ((cb+1)*N) (Wide.project a) := by
    intro i
    have hx := (inputMass_bound a i).trans (hi.trans hVN)
    change (a.stacks i).length ≤ _
    nlinarith
  have hb' : WordBound ((cb+1)*N) (bankOutput a p w tail) := by
    intro i
    have hx := hbN i
    nlinarith
  have hcost := budget_overhead_le a p he w tail ((cb+1)*N) ha hb'
  have hout := result_wordBound a p he w tail ((cb+1)*N) ha hb'
  have hcap : (cb+1)*N ≤ combinedConstant cc cb*N := by
    unfold combinedConstant
    nlinarith
  constructor
  · change budget a p w tail ≤ combinedConstant cc cb*N
    unfold combinedConstant
    nlinarith
  · intro i
    exact (hout i).trans hcap

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
