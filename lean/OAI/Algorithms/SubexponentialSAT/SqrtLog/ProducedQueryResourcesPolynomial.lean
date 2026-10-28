import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesConstructor

namespace OAI.Algorithms

/-! Fixed scalar caps for the actual producer bounds. The measure here is a
numerical magnitude, never a bucket table or sparse dictionary byte length. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources

 def capExponent (C d : ℕ) := C+5*d+8

 theorem polynomial_cap (C d n M : ℕ) (hn : 2 ≤ n) (hM : M ≤ n^4) :
    C*(M+1)^d ≤ (n+1)^capExponent C d := by
  have hc : C ≤ (n+1)^C := (CodeSetupCost.self_le_three_pow C).trans
    (Nat.pow_le_pow_left (by omega) _)
  have hp : n^4 ≤ (n+1)^4 := Nat.pow_le_pow_left (by omega) _
  have h1 : 1 ≤ (n+1)^4 := Nat.one_le_pow _ _ (by omega)
  have hm : M+1 ≤ (n+1)^5 := by
    rw [show (5:ℕ)=4+1 by decide,pow_succ]
    nlinarith
  calc
    _ ≤ (n+1)^C*((n+1)^5)^d := Nat.mul_le_mul hc (Nat.pow_le_pow_left hm _)
    _ = (n+1)^(C+5*d) := by rw [←pow_mul,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by unfold capExponent; omega)

 theorem make_scalar_cap (q : LeafQueryFrontend.Query) (k B rows size C0 d0 qi e C d n M : ℕ)
    (hn : 2 ≤ n) (hqn : ambient q=n) (hM : M ≤ n^4) (he : capExponent C d ≤ e) :
    C*(M+1)^d ≤ (make q k B rows size C0 d0 qi e).ordinary ∧
    C*(M+1)^d ≤ (make q k B rows size C0 d0 qi e).bits := by
  have hh := (polynomial_cap C d n M hn hM).trans
    (Nat.pow_le_pow_right (by omega : 1 ≤ n+1) he)
  simpa only [make,hqn] using And.intro hh hh

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
