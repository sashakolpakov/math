import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesEnvelope

namespace OAI.Algorithms

/-! Uniform conversion of the measured query polynomial to the target.
The source-byte parameter is universally quantified after the cutoff. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend CostAssembly
open scoped Topology
open SubexponentialSAT.MulticolorTypes

def runtimeCoefficient (C e : ℕ) : ℝ := ((C:ℝ)+1)*18^e
def runtimeExponent (k qi e : ℕ) : ℝ :=
  1+(e:ℝ)*exponentConstant k (LeafScopeResourceBounds.resourceExponent qi+1)

theorem runtimeCoefficient_pos (C e : ℕ) : 0 < runtimeCoefficient C e := by
  unfold runtimeCoefficient
  positivity

theorem runtimeExponent_pos (k qi e : ℕ) : 0 < runtimeExponent k qi e := by
  unfold runtimeExponent exponentConstant
  positivity

theorem padded_envelope_runtime (k qi C e n X : ℕ) (p : Resources)
    (h : (nativeEnvelope k n e ((ordinaryExponent+1)*e) p:ℝ) ≤
      (18:ℝ)^e*(2:ℝ)^(runtimeExponent k qi e*Statement.runtimeScale n)) :
    ((C*(X+1)^e*(n+1)^((ordinaryExponent+1)*e)*(assembledWork k n p+1)^e:ℕ):ℝ) ≤
      Statement.runtimeBound (runtimeCoefficient C e) (runtimeExponent k qi e) e X n := by
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (C:ℝ)*((X:ℝ)+1)^e by positivity)
  have hC : (C:ℝ) ≤ (C:ℝ)+1 := by linarith
  unfold Statement.runtimeBound runtimeCoefficient
  unfold nativeEnvelope at hh
  push_cast at hh ⊢
  calc
    _ ≤ (C:ℝ)*((X:ℝ)+1)^e*((18:ℝ)^e*
        (2:ℝ)^(runtimeExponent k qi e*Statement.runtimeScale n)) := by
      convert hh using 1 ; ring
    _ ≤ ((C:ℝ)+1)*18^e*((X:ℝ)+1)^e*
        (2:ℝ)^(runtimeExponent k qi e*Statement.runtimeScale n) := by
      have hm := mul_le_mul_of_nonneg_right hC
        (show 0 ≤ ((X:ℝ)+1)^e*((18:ℝ)^e*
          (2:ℝ)^(runtimeExponent k qi e*Statement.runtimeScale n)) by positivity)
      convert hm using 1 <;> ring

theorem eventually_origin_runtime (k qi C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a::tail).Nodup → (∀z,z∈a::tail) → ∀ X : ℕ,
        ((C*(X+1)^e*(n+1)^((ordinaryExponent+1)*e)*
          (assembledWork k n (resources q k B qi hg a tail)+1)^e:ℕ):ℝ) ≤
        Statement.runtimeBound (runtimeCoefficient C e) (runtimeExponent k qi e) e X n := by
  filter_upwards [eventually_resourceEnvelope k qi e ((ordinaryExponent+1)*e)]
    with n hn q B hv hqn ho hB hc hBL hg a tail haN haC X
  exact padded_envelope_runtime k qi C e n X _
    (hn q B hv hqn ho hB hc hBL hg a tail haN haC)

theorem origin_runtime_uniform_cutoff (k qi C e : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (q : Query) (B : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a::tail).Nodup → (∀z,z∈a::tail) → ∀ X : ℕ,
        ((C*(X+1)^e*(n+1)^((ordinaryExponent+1)*e)*
          (assembledWork k n (resources q k B qi hg a tail)+1)^e:ℕ):ℝ) ≤
        Statement.runtimeBound (runtimeCoefficient C e) (runtimeExponent k qi e) e X n :=
  Filter.eventually_atTop.mp (eventually_origin_runtime k qi C e)

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end

end OAI.Algorithms
