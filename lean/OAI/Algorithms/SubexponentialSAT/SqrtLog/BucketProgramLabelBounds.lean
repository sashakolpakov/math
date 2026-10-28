import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramLabelLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramEnumeration

namespace OAI.Algorithms

/-! Polynomial work per head assignment, hence only 2^h labels. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Label
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def keyBound (W : List Bool) (h m B : ℕ) : ℕ := m*(2*(widthBound W h B+1)+1)
def matrixBound (h m B : ℕ) : ℕ := m*(2*(h*(2*B+1))+1)
def signatureBound (W : List Bool) (h m B : ℕ) : ℕ := m*(signatureRowBound W h B+2)+1

def stepBound (W : List Bool) (h m B n : ℕ) : ℕ :=
  1+(9*h+7)+(7*matrixBound h m B+5)+(signatureBound W h m B+2)+
  100*(n+1)*(h+1)+(7*keyBound W h m B+5)+(8*keyBound W h m B+8)+2+
  (8*n+8)+(8*keyBound W h m B+8)+(2*h+3)

theorem matrix_length_bound (rows : List (List (List Bool))) (h B : ℕ)
    (hl : ∀ row∈rows,row.length=h) (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B) :
    (words (rows.map words)).length ≤ matrixBound h rows.length B := by
  have hr : ∀ r∈rows.map words,r.length ≤ h*(2*B+1) := by
    intro r hr
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hr
    simpa [hl row hrow] using words_length_bound row B (hb row hrow)
  simpa [matrixBound] using words_length_bound (rows.map words) (h*(2*B+1)) hr

theorem stepCost_bound (W bits : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n B : ℕ) (hrows : ∀ row∈rows,row.length=bits.length)
    (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B) (hlen : js.length=bits.length)
    (hjs : ∀ j∈js,j < n) :
    stepCost W bits rows js n ≤ stepBound W bits.length rows.length B n := by
  have hm := matrix_length_bound rows bits.length B hrows hb
  have hk := signatureValue_length_bound W bits rows B hrows hb
  have hs := signatureCost_bound W bits rows B hrows hb
  have ht := HeadScatterProgram.totalCost_polynomial n js bits hlen hjs
  rw [hlen] at ht
  unfold stepCost stepBound matrixBound keyBound signatureBound at *
  change (key W bits rows).length ≤ _ at hk
  omega

theorem cost_bound (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h B : ℕ) (pending : List (List Bool))
    (hrows : ∀ row∈rows,row.length=h) (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n)
    (hpending : ∀ bits∈pending,bits.length=h) :
    cost W rows js n pending ≤ pending.length*(stepBound W h rows.length B n+2)+1 := by
  unfold cost
  suffices hs : (pending.map (fun bits => stepCost W bits rows js n+2)).sum ≤
      pending.length*(stepBound W h rows.length B n+2) by omega
  induction pending with
  | nil => simp
  | cons bits rest ih =>
      have hl := hpending bits (by simp)
      have hx := stepCost_bound W bits rows js n B
        (by intro row hr; rw [hrows row hr,hl]) hb (hlen.trans hl.symm) hjs
      rw [hl] at hx
      have ht := ih (fun bits hm => hpending bits (by simp [hm]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

/-- Fixed program bound for all Boolean assignments to the supplied h head
coordinates. The original ambient n occurs only polynomially. -/
theorem headLabelProgram_runsIn (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (js : List ℕ) (n h B : ℕ)
    (hrows : ∀ row∈rows,row.length=h) (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ rf, RunsIn program (2^h*(stepBound W h rows.length B n+2)+3)
      ((state regs W rows js n (assignments h) [] [false]).withPC (some program.entry))
      ((state rf W rows js n [] (recordOutput W rows js n (assignments h) [])
        (keyOutput W rows (assignments h) [false])).withPC none) := by
  have ha : ∀ bits∈assignments h,bits.length=h := fun bits hm => assignment_width hm
  obtain ⟨rf,t,ht,he⟩ := program_runsIn regs W rows js n (assignments h) [] [false]
    (by intro bits hm row hr; rw [hrows row hr,ha bits hm])
    (by intro bits hm; rw [hlen,ha bits hm]) hjs
  have hc := cost_bound W rows js n h B (assignments h) hrows hb hlen hjs ha
  rw [assignments_length] at hc
  exact ⟨rf,t,by omega,he⟩

end SubexponentialSAT.SqrtLog.BucketProgram.Label

end OAI.Algorithms
