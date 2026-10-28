import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeQueryInputs
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRuntimeBound

namespace OAI.Algorithms

/-! One uniform all-Origin query cutoff and its literal source-byte budget.
The queue/accumulator are excluded because the query replay frames them. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram ProducedQueryResources Filter
open scoped Topology
open SubexponentialSAT.MulticolorTypes

def queryBytes (q : LeafQueryFrontend.Query) : ℕ :=
  (Encoding.encodeList id q.clauses).length+
    (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length+
    q.modulus.length+q.width.length+q.ambient.length+q.index.length

theorem sourceBytes_eq (q : LeafQueryFrontend.Query) (a : Query.Data)
    (hs : Query.Sources q a) (hr : a.stacks 321=q.index.reverse) :
    Query.Carried.sourceBytes a=queryBytes q := by
  simp only [Query.Carried.sourceBytes,queryBytes,hs.formula,hs.rows,hs.modulus,
    hs.width,hs.ambient,hr,List.length_reverse]

def queryLimit (k qi C e : ℕ) (q : LeafQueryFrontend.Query) : ℕ :=
  Nat.ceil (Statement.runtimeBound (runtimeCoefficient C e) (runtimeExponent k qi e)
    e (queryBytes q) (ambient q))

structure RuntimeFacts (q : LeafQueryFrontend.Query) (k B qi C e : ℕ) : Prop where
  guard : LeafParametersProgram.Guard (q.input k)
  small : SmallInputs q k (ambient q)
  cost : ∀ (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
    (first::tail).Nodup → (∀z,z∈first::tail) →
    C*(queryBytes q+1)^e*(ambient q+1)^((ordinaryExponent+1)*e)*
      (CostAssembly.assembledWork k (ambient q) (resources q k B qi hg first tail)+1)^e ≤
      queryLimit k qi C e q

theorem eventually_runtimeFacts (k qi C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : LeafQueryFrontend.Query) (B : ℕ),
      q.Valid → ambient q=n → Origin q k B →
      0 < B → q.clauses.length ≤ n*B → B ≤ Asymptotic.L n^qi →
      RuntimeFacts q k B qi C e := by
  filter_upwards [eventually_resources_bounds k qi,eventually_origin_runtime k qi C e]
    with n hres htime q B hv hqn ho hB hc hBL
  obtain ⟨hg,hs,_⟩ := hres q B hv hqn ho hB hc hBL
  refine ⟨hg,?_,?_⟩
  · simpa only [hqn] using hs
  · intro hg first tail hN hC
    have hb := htime q B hv hqn ho hB hc hBL hg first tail hN hC (queryBytes q)
    rw [←hqn] at hb
    have hh := hb.trans (Nat.le_ceil _)
    exact_mod_cast hh

theorem RuntimeFacts.source_cost {q : LeafQueryFrontend.Query} {k B qi C e : ℕ}
    (h : RuntimeFacts q k B qi C e) (a : Query.Data)
    (hs : Query.Sources q a) (hr : a.stacks 321=q.index.reverse)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (hN : (first::tail).Nodup) (hC : ∀z,z∈first::tail) :
    C*(Query.Carried.sourceBytes a+1)^e*(ambient q+1)^((ordinaryExponent+1)*e)*
      (CostAssembly.assembledWork k (ambient q) (resources q k B qi hg first tail)+1)^e ≤
      queryLimit k qi C e q := by
  rw [sourceBytes_eq q a hs hr]
  exact h.cost hg first tail hN hC

end SubexponentialSAT.SqrtLog.OuterNativeServices

end

end OAI.Algorithms
