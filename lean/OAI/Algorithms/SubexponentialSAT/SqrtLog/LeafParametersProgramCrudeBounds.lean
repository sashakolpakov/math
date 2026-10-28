import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

open Asymptotic

def magnitude (x : Input) : ℕ :=
  x.ambient+x.freeCount+x.clauses+x.occurrence+x.arity+x.factors+x.width+x.incidences+16

def loopCap (x : Input) : ℕ := 1000000*(magnitude x)^6

theorem magnitude_ge (x : Input) :
    16 ≤ magnitude x ∧ x.freeCount ≤ magnitude x ∧ x.occurrence ≤ magnitude x := by
  dsimp [magnitude]
  omega

theorem L_le_magnitude (x : Input) : L x.freeCount ≤ 2*magnitude x := by
  have h := Nat.log2_le_self (x.freeCount+16)
  dsimp [L, magnitude]
  omega

theorem energy_le_magnitude (x : Input) :
    layoutEnergy x.freeCount x.occurrence ≤ 513*(magnitude x)^4 := by
  let H := magnitude x
  have hH : 1 ≤ H := by dsimp [H]; have := magnitude_ge x; omega
  have hL := L_le_magnitude x
  have hr := (layoutR_le_L x.freeCount).trans hL
  have hb := (magnitude_ge x).2.2
  have hlog := Nat.log2_le_self (64*x.occurrence*layoutR x.freeCount*(L x.freeCount)^2)
  have hprod : 64*x.occurrence*layoutR x.freeCount*(L x.freeCount)^2 ≤ 512*H^4 := by
    calc
      _ ≤ 64*H*(2*H)*(2*H)^2 := by gcongr
      _ = _ := by ring
  have hpow : 1 ≤ H^4 := one_le_pow₀ hH
  dsimp [layoutEnergy]
  change Nat.log2 _+1 ≤ 513*H^4
  omega

theorem loop_operands_le_cap (x : Input) :
    16 ≤ loopCap x ∧ L x.freeCount ≤ loopCap x ∧
    2*layoutQ x.freeCount ≤ loopCap x ∧
    128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ loopCap x ∧
    Nat.log2 (layoutQ x.freeCount)+2 ≤ loopCap x := by
  let H := magnitude x
  have hH : 16 ≤ H := (magnitude_ge x).1
  have hL := L_le_magnitude x
  have hQ : layoutQ x.freeCount ≤ 2*H := (Nat.div_le_self _ _).trans hL
  have hE := energy_le_magnitude x
  have hlog := Nat.log2_le_self (layoutQ x.freeCount)
  have hp1 : H ≤ H^6 := Nat.le_self_pow (by decide) _
  have hp5 : H^5 ≤ H^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp0 : 1 ≤ H^6 := one_le_pow₀ (by omega)
  have hroot : 128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ 131328*H^5 := by
    calc
      _ ≤ 128*(2*H)*(513*H^4) := by gcongr
      _ = _ := by ring
  change 16 ≤ 1000000*H^6 ∧ _ ∧ _ ∧ _ ∧ _
  dsimp [loopCap]
  change 16 ≤ 1000000*H^6 ∧ L x.freeCount ≤ 1000000*H^6 ∧
    2*layoutQ x.freeCount ≤ 1000000*H^6 ∧
    128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ 1000000*H^6 ∧
    Nat.log2 (layoutQ x.freeCount)+2 ≤ 1000000*H^6
  omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
