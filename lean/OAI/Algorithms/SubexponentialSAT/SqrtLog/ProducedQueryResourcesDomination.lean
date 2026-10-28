import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesHeight
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesPolynomial

namespace OAI.Algorithms

/-! Literal scalar and all-row sizes fit the ordinary caps. The coefficient
height's binary size is bounded; its potentially large value is not treated
as an ordinary scalar. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open LeafQueryFrontend

 theorem coefficient_power_le (C d n e : ℕ) (hn : 2 ≤ n) (he : C+d ≤ e) :
    C*(n+1)^d ≤ (n+1)^e := by
  have hc : C ≤ (n+1)^C := (CodeSetupCost.self_le_three_pow C).trans
    (Nat.pow_le_pow_left (by omega) _)
  calc
    _ ≤ (n+1)^C*(n+1)^d := Nat.mul_le_mul_right _ hc
    _ = (n+1)^(C+d) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

 theorem literal_scalar_caps (q : Query) (k B rows size C d qi e n : ℕ)
    (hv : q.Valid) (hn : 2 ≤ n) (hqn : ambient q=n) (hs : SmallInputs q k n)
    (hg : LeafParametersProgram.Guard (q.input k)) (he : 13 ≤ e) :
    LeafParametersProgram.magnitude (q.input k) ≤ (make q k B rows size C d qi e).ordinary ∧
    (q.input k).incidences ≤ (make q k B rows size C d qi e).ordinary ∧
    n ≤ (make q k B rows size C d qi e).ordinary ∧
    Nat.size (matrixHeight q k) ≤ (make q k B rows size C d qi e).bits := by
  have hp4 : n^4 ≤ (n+1)^e := (Nat.pow_le_pow_left (by omega) 4).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hp2 : n^2 ≤ (n+1)^e := (Nat.pow_le_pow_left (by omega) 2).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hp1 : n ≤ (n+1)^e := (show n ≤ n+1 by omega).trans
    (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ n+1) (show 1 ≤ e by omega))
  have hheight := (matrixHeight_size q k n hv hqn hs hg).trans
    (coefficient_power_le 11 2 n e hn (by omega))
  simpa only [make,hqn] using And.intro (hs.magnitude.trans hp4)
    (And.intro (hs.incidences.trans hp2) (And.intro hp1 hheight))

/-- Padding is charged as an explicit input factor. This elementary product
inequality never puts a generated dictionary into the ordinary resource. -/
 theorem input_sum_power (input n d : ℕ) :
    (input+n+1)^d ≤ (input+1)^d*(n+1)^d := by
  rw [←mul_pow]
  exact Nat.pow_le_pow_left (by nlinarith) _

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
