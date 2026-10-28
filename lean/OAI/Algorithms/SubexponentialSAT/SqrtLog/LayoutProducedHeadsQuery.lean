import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeadsScope
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBoundsQuery

namespace OAI.Algorithms

/-! The maximum size of an actually emitted head list is bounded directly
from a query's integer guards. Ambient owner IDs remain unchanged, while
all layout parameters use the measured free-variable count. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open SubexponentialSAT.MulticolorTypes LeafParametersProgram LeafQueryFrontend

 theorem query_low_bytes (q : Query) (k : ℕ) (hg : Guard (q.input k)) :
    q.forward.map Bool.not = HeadIdentifierProgram.lowBits
      (fun v : Fin (LeafProgram.Query.packingProblem q k hg).n =>
        !(q.forward.getD v.val false)) := by
  have hl : q.forward.length=(LeafProgram.Query.packingProblem q k hg).n := by
    simp [Query.forward,highMask,LeafProgram.Query.packingProblem]
  apply List.ext_getElem
  · simp [HeadIdentifierProgram.lowBits,hl]
  · intro i hi hj
    have hi' : i < q.forward.length := by simpa only [List.length_map] using hi
    simp [HeadIdentifierProgram.lowBits,List.getElem?_eq_getElem hi']

/-- This is the actual finite maximum over all node/head addresses, not an
assumed head-size parameter. No validity premise beyond the checked integer
guards is needed for these structurally deduplicated query scopes. -/
 theorem query_max_bound_rat (q : Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    let p := LeafProgram.Query.packingProblem q k hg
    (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ)) := by
  let p := LeafProgram.Query.packingProblem q k hg
  have hg' := hg
  change (maxSelected p.n p.Q p.r ((p.words a tail).map _)
    (q.forward.map Bool.not) : ℚ) ≤ _
  rw [query_low_bytes q k hg]
  rcases hg with ⟨hm,hmn,hc,hocc,har,hmi,hQ,hRQ,hlarge,hhead⟩
  have hi : p.incidences=(q.input k).incidences :=
    LeafProgram.Query.packingProblem_incidences q k hg'
  have hn : p.n=(q.input k).ambient := rfl
  apply problem_head_max_bound p a tail haN haC (q.input k).occurrence (q.input k).arity
  · exact LeafPackingFiberBounds.query_owner_fiber_le q k hg'
  · exact LeafPackingFiberBounds.query_factor_fiber_le q k hg'
  · omega
  · omega
  · change 4*((q.input k).occurrence+(q.input k).arity)*
      ((produce (q.input k)).r^(2*(produce (q.input k)).Q))^2*
        (produce (q.input k)).epsilonDen^2 ≤ p.incidences
    rw [hi]
    exact hlarge
  · change 16*(produce (q.input k)).Q*(produce (q.input k)).r^2 ≤ p.n
    rw [hn]
    exact hhead.trans hmn

/-- Form consumed by the produced-query resource envelope: ambient head
sizes with the free-variable layout schedule. -/
 theorem query_max_bound_real (q : Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    let p := LeafProgram.Query.packingProblem q k hg
    (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℝ) ≤
      2*(BinaryArithmetic.toNat q.ambient:ℝ)/Asymptotic.layoutR (q.input k).freeCount := by
  let p := LeafProgram.Query.packingProblem q k hg
  have hq : (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ)) :=
    query_max_bound_rat q k hg a tail haN haC
  have hrq : (0:ℚ) < p.r := by exact_mod_cast p.hr
  have hm := (le_div_iff₀ (by positivity : (0:ℚ) < 2*(p.r:ℚ))).mp hq
  have hmR : (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℝ)*(2*(p.r:ℝ)) ≤ 3*(p.n:ℝ) := by
    exact_mod_cast hm
  have hr : (0:ℝ) < p.r := by exact_mod_cast p.hr
  change (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℝ) ≤ 2*(p.n:ℝ)/(p.r:ℝ)
  apply (le_div_iff₀ hr).mpr
  nlinarith [show (0:ℝ) ≤ (p.n:ℝ) by positivity]

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end

end OAI.Algorithms
