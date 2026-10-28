import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramNormalize

namespace OAI.Algorithms

/-! Uniform polynomial accounting for all primitive readout loops. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def uniformSlotBudget (B d n t J W N : ℕ) : ℕ :=
  100*(N+1)*(W+d*B+n+t+J+3)+MomentsProgram.Dictionary.codeBranchBudget B d+8*(d*B)+100

theorem slotBudget_le (B d n t J W u z : ℕ)
    (entries : List (List Bool × List Bool))
    (hk : ∀ a∈entries, a.1.length ≤ W) (hc : ∀ a∈entries, a.2.length ≤ d*B)
    (hu : u ≤ t) (hz : z ≤ J) :
    slotBudget B d n u z entries ≤ uniformSlotBudget B d n t J W entries.length := by
  have hr := MomentsProgram.Dictionary.rawEntries_length_le entries W (d*B) hk hc
  have hl := Squarefree.Program.lookupBudget_bound
    (Squarefree.encodeIndex (⟨u,z,∅⟩ : Squarefree.Index (Fin n))) entries W (d*B) hk hc
  have hq : (Squarefree.encodeIndex (⟨u,z,∅⟩ : Squarefree.Index (Fin n))).length ≤ n+t+J+2 := by
    simp only [Squarefree.encodeIndex_length]
    omega
  have hmul := Nat.mul_le_mul_left entries.length hq
  have hinside : 35*W+31*(d*B)+9*(n+t+J)+76 ≤
      100*(W+d*B+n+t+J+3) := by omega
  have hscaled := Nat.mul_le_mul_left entries.length hinside
  have hrest : 9*(n+u+z)+62 ≤ 100*(W+d*B+n+t+J+3)+100 := by omega
  dsimp [slotBudget,accumulateBudget,fetchBudget,uniformSlotBudget]
  simp only [Squarefree.encodeIndex_length] at hl hq hmul
  nlinarith

theorem innerBudget_le (B d n t J W z u k : ℕ)
    (entries : List (List Bool × List Bool))
    (hk : ∀ a∈entries, a.1.length ≤ W) (hc : ∀ a∈entries, a.2.length ≤ d*B)
    (hu : u+k ≤ t) (hz : z ≤ J) :
    innerBudget B d n z entries u k ≤ k*(uniformSlotBudget B d n t J W entries.length+2)+2 := by
  induction k generalizing u with
  | zero => simp [innerBudget]
  | succ k ih =>
      have hs := slotBudget_le B d n t J W u z entries hk hc (by omega) hz
      have hi := ih (u+1) (by omega)
      simp only [innerBudget]
      nlinarith

theorem outerBudget_le (B d n t J W z k : ℕ)
    (entries : List (List Bool × List Bool))
    (hk : ∀ a∈entries, a.1.length ≤ W) (hc : ∀ a∈entries, a.2.length ≤ d*B)
    (hz : z+k ≤ J) :
    outerBudget B d n t entries z k ≤
      k*(t*(uniformSlotBudget B d n t J W entries.length+2)+10*(d*B)+9*t+22)+2 := by
  induction k generalizing z with
  | zero => simp [outerBudget]
  | succ k ih =>
      have hs := innerBudget_le B d n t J W z 0 t entries hk hc (by omega) (by omega)
      have hi := ih (z+1) (by omega)
      simp only [outerBudget,rowBudget]
      nlinarith

def uniformReadoutBudget (B d n t J W N : ℕ) : ℕ :=
  J*(t*(uniformSlotBudget B d n t J W N+2)+10*(d*B)+9*t+22)+
    3*(J*(d*B))+9*J+13*n+24

theorem readoutBudget_polynomial (B d n t J W : ℕ)
    (entries : List (List Bool × List Bool))
    (hk : ∀ a∈entries, a.1.length ≤ W) (hc : ∀ a∈entries, a.2.length ≤ d*B) :
    readoutBudget B d n t J entries+1 ≤ uniformReadoutBudget B d n t J W entries.length := by
  have h := outerBudget_le B d n t J W 0 J entries hk hc (by omega)
  dsimp [readoutBudget,uniformReadoutBudget]
  omega

theorem program_runsIn_polynomial {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count t J shape : List Bool) (W : ℕ)
    (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n)
    (hk : ∀ a∈entries, (Squarefree.encodeIndex a.1).length ≤ W) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let bits := outputBits p e M cache entries t.length zero 0 J.length
    ∃ rr, RunsIn program (uniformReadoutBudget (baseWidth p e) d n t.length J.length W entries.length)
      ((wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
        (inputHigh (RingProgram.flat zero) t J shape)).withPC (some program.entry))
      ((wideState rr {MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [] with out:=bits}
        (inputHigh (RingProgram.flat zero) t J shape)).withPC none) := by
  dsimp only
  let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
  have hk' : ∀ a∈encoded, a.1.length ≤ W := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact hk x hx
  have hc' : ∀ a∈encoded, a.2.length ≤ d*baseWidth p e := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    simp [RingProgram.flat_length]
  have hb := readoutBudget_polynomial (baseWidth p e) d n t.length J.length W encoded hk' hc'
  have hl : encoded.length=entries.length := by simp [encoded,Squarefree.Program.encodeDictionary]
  rw [hl] at hb
  obtain ⟨rr,tm,ht,he⟩ := program_runsIn p e M cache entries zero regs width count t J shape hc hw hs
  exact ⟨rr,tm,ht.trans hb,he⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
