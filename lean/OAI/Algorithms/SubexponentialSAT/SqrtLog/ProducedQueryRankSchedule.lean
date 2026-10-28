import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankCoverage

namespace OAI.Algorithms

/-! Scheduled rank of the literal native packing. The intermediate scan
premises are discharged for produced queries in the final certificate. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram
open BucketProgram.ProducedRank

/-- This finite maximum uses all actual node indices and all actual heads. -/
def labelRows (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (R : ℕ) (low : List Bool) : ℕ :=
  CostAssembly.maxTotalRank Finset.univ (actualRank (packing p a tail) (owner p)
    (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q R) R (rows p a tail) low)

def queryLow (q : LeafQueryFrontend.Query) : List Bool := q.forward.map Bool.not

 theorem queryLow_eq (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) :
    queryLow q=HeadIdentifierProgram.lowBits (fun v : Fin (LeafProgram.Query.packingProblem q k hg).n =>
      !(q.forward.getD v.val false)) := by
  have hl : q.forward.length=(LeafProgram.Query.packingProblem q k hg).n := by
    simp [LeafQueryFrontend.Query.forward,LeafQueryFrontend.highMask,LeafProgram.Query.packingProblem]
  apply List.ext_getElem
  · simp [queryLow,HeadIdentifierProgram.lowBits,hl]
  · intro i hi hj
    have hi' : i < q.forward.length := by simpa only [queryLow,List.length_map] using hi
    simp [queryLow,HeadIdentifierProgram.lowBits,List.getElem?_eq_getElem hi']

/-- The actual query parameters fix the rank function; no rank field is input. -/
def queryLabelRows (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)) : ℕ :=
  labelRows (LeafProgram.Query.packingProblem q k hg) a tail (produce (q.input k)).R (queryLow q)

 theorem query_epsilon (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) :
    1/((LeafProgram.Query.packingProblem q k hg).s:ℚ)=
      Asymptotic.layoutEpsilon (q.input k).freeCount (q.input k).occurrence := rfl

 theorem query_rank_budget_of_scan (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail)
    (hB : ∀ v,(Finset.univ.filter fun i => owner (LeafProgram.Query.packingProblem q k hg) i=v).card ≤
      (q.input k).occurrence)
    (hb : ∀ e,(Finset.univ.filter fun i => factor (LeafProgram.Query.packingProblem q k hg) i=e).card ≤
      (q.input k).arity)
    (hD : (LeafProgram.Query.packingProblem q k hg).incidences ≤
      (q.input k).occurrence*(q.input k).freeCount) :
    16*(Asymptotic.layoutR (q.input k).freeCount:ℝ)*(Asymptotic.L (q.input k).freeCount:ℝ)^2*
      (queryLabelRows q k hg a tail:ℝ) ≤ (q.input k).freeCount := by
  let p := LeafProgram.Query.packingProblem q k hg
  rcases hg with ⟨hm,hmn,hc,hocc,har,hmi,hQ,hRQ,hlarge,hhead⟩
  have hi : p.incidences=(q.input k).incidences := LeafProgram.Query.packingProblem_incidences q k _
  have hn : p.n=(q.input k).ambient := rfl
  have hcov := packing_coverage p a tail haN haC (q.input k).occurrence (q.input k).arity hB hb
    (by omega) (by omega)
    (by
      change 4*((q.input k).occurrence+(q.input k).arity)*
        ((produce (q.input k)).r^(2*(produce (q.input k)).Q))^2*
          (produce (q.input k)).epsilonDen^2 ≤ p.incidences
      rw [hi]
      exact hlarge)
    (by change 16*(produce (q.input k)).Q*(produce (q.input k)).r^2 ≤ p.n
        rw [hn]; exact hhead.trans hmn)
  change (1-Asymptotic.layoutEpsilon (q.input k).freeCount (q.input k).occurrence)*
    (p.incidences:ℚ) ≤ (packing p a tail).blockCount*
      (Fintype.card (UniversalType p.r p.Q 1):ℚ) at hcov
  exact actualMax_rank_budget (packing p a tail) (owner p)
    (fun t v=>words p a tail (.inl v) t) (packing_head p a tail)
    (produce (q.input k)).R (rationalDenominator (produce (q.input k)).R) rfl
    (rationalUnits p.Q) (rows p a tail) (queryLow q) Finset.univ
    (fun t _ g v hv=>selected_head p a tail (queryLow q) t g v hv)
    (q.input k).freeCount (q.input k).occurrence hocc hD
    (produce_r_ge_two _) hQ (produce_R_ge_four _) hRQ
    (Asymptotic.layoutEpsilon_pos _ hocc) (guard_spectral _ ⟨hm,hmn,hc,hocc,har,hmi,hQ,hRQ,hlarge,hhead⟩)
    hcov

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
