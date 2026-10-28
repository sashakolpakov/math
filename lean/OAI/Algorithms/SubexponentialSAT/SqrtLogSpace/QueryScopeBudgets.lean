import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyHighMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsPolylog
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyUniform
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsUniform
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramCrudeBounds

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.LeafStatisticsProgram
open SqrtLog.LeafScopeResourceBounds SqrtLog.CostAssembly
open scoped Topology

/-- Raw retained scope resources suffice for every guard. This theorem is
independent of candidate order or an old materialized selector history. -/
theorem eventually_raw_scope_guards (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (scopes : List (List ℕ)) (m B : ℕ),
      0 < m → m ≤ n * B → B ≤ L n ^ qi →
      scopes.length ≤ 3 * n + HashSelect.loopCap n m + 2 →
      HighIncidenceProgram.Prepare.mass scopes ≤
        (3 * n * SparseCode.degreeBound m B +
          (HashSelect.loopCap n m + 1) * SparseCode.distanceDenom m B + 1) * k →
      (∀ row ∈ scopes, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) →
      (∀ row ∈ scopes, row.Nodup) →
      let mask := forwardHighMask scopes n (Nat.sqrt (L n) + 1)
      let x := measuredParameterInput scopes mask m k
      LeafParametersProgram.Guard x ∧ x.freeCount ≤ n ∧ n ≤ 2 * x.freeCount ∧
        x.factors ≤ 4 * n + HashSelect.loopCap n m + 2 ∧
        x.occurrence ≤ L x.freeCount ^ (resourceExponent qi + 1) ∧
        x.arity ≤ L x.freeCount ^ (resourceExponent qi + 1) := by
  filter_upwards [eventually_forwardHighMask_guards (statCoefficient k qi) (resourceExponent qi),
    eventually_sparse_parameter_bounds qi,
    eventually_residual_polynomial (statCoefficient k qi) (resourceExponent qi),
    eventually_ge_atTop (1 : ℕ)] with n hguard hparameters hpoly hn scopes m B hm hmb hB hlen hmass har hnd
  let mask := forwardHighMask scopes n (Nat.sqrt (L n) + 1)
  have hmask : forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes n.bits
      (Nat.sqrt (L n) + 1).bits) n = mask := by
    simp [mask, forwardMask, forwardHighMask, HighIncidenceProgram.Prepare.cut,
      HighIncidenceProgram.Prepare.mass, ArithmeticExpressionSupport.bits_value]
  have hs := measured_polylog n m B k qi (by omega) hmb hB
    (hparameters m B hmb hB).1 scopes n.bits (Nat.sqrt (L n) + 1).bits
    (ArithmeticExpressionSupport.bits_value n) (ArithmeticExpressionSupport.bits_value _)
    hmass har
  rw [hmask] at hs
  have hfree : (measured scopes mask).free ≤ n :=
    (LeafStatisticsProgram.free_le_ambient scopes mask).trans_eq
      (forwardHighMask_length scopes n _)
  have hhalf : n ≤ 2 * (measured scopes mask).free :=
    forwardHighMask_retains_half scopes n _ (by omega) (highThreshold_ge_two n)
  have hfac := measured_factors_le scopes mask
  rw [forwardHighMask_length] at hfac
  refine ⟨hguard scopes m k hm hnd hs.1 hs.2, hfree, hhalf, ?_,
    hpoly _ _ hhalf hs.1, hpoly _ _ hhalf hs.2⟩
  change scopes.length + (measured scopes mask).uncovered ≤ _
  omega

/-- A crude input-polynomial bound for the actual measured fields requires
neither successful guards nor any selector provenance. Neutral singleton
factors and every raw incidence are included. -/
theorem raw_scope_magnitude_le (scopes : List (List ℕ)) (n m k tau S : ℕ)
    (hn : 0 < n) (hS : 1 ≤ S) (hnS : n ≤ S) (hmS : m ≤ S) (hkS : k ≤ S)
    (hcount : scopes.length ≤ S) (hmass : HighIncidenceProgram.Prepare.mass scopes ≤ S)
    (harity : ∀ row ∈ scopes, row.length ≤ S) (htau : tau ≤ S) :
    LeafParametersProgram.magnitude
      (measuredParameterInput scopes (forwardHighMask scopes n tau) m k) ≤ 26 * S ^ 2 := by
  let mask := forwardHighMask scopes n tau
  have hmask : forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes n.bits tau.bits) n = mask := by
    simp [mask, forwardMask, forwardHighMask, HighIncidenceProgram.Prepare.cut,
      HighIncidenceProgram.Prepare.mass, ArithmeticExpressionSupport.bits_value]
  have hfree := LeafStatisticsProgram.free_le_ambient scopes mask
  have hlen : mask.length = n := forwardHighMask_length scopes n tau
  rw [hlen] at hfree
  have hocc := measured_occurrence_of_mass scopes n.bits tau.bits
    (HighIncidenceProgram.Prepare.mass scopes)
    (by simpa only [ArithmeticExpressionSupport.bits_value] using hn)
    (by simpa only [ArithmeticExpressionSupport.bits_value] using
      Nat.le_mul_of_pos_left (HighIncidenceProgram.Prepare.mass scopes) hn)
  rw [ArithmeticExpressionSupport.bits_value, hmask] at hocc
  simp only [ArithmeticExpressionSupport.bits_value] at hocc
  have hp : HighIncidenceProgram.Prepare.mass scopes * tau ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hmass htau
  have h1 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS
  have hoccS : (measured scopes mask).occurrence ≤ S ^ 2 :=
    hocc.trans (max_le h1 hp)
  have har := measured_arity_le scopes mask S harity
  rw [max_eq_left hS] at har
  have hfac := measured_factors_le scopes mask
  rw [hlen] at hfac
  have hinc := measured_incidences_le scopes mask
  rw [hlen] at hinc
  have hmass' : slots scopes ≤ S := hmass
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by decide) S
  change LeafParametersProgram.magnitude (measuredParameterInput scopes mask m k) ≤ _
  unfold LeafParametersProgram.magnitude measuredParameterInput measuredArity
  rw [hlen]
  dsimp only
  omega

/-- Uniform ordinary scalar caps bound the entire measured input for every
raw history or trial; the threshold is computed from the declared ambient. -/
theorem raw_resources_magnitude_polynomial (scopes : List (List ℕ))
    (n m k D P rounds S : ℕ) (hn : 0 < n) (hS : 1 ≤ S)
    (hnS : n ≤ S) (hmS : m ≤ S) (hkS : k ≤ S) (hD : D ≤ S)
    (hP : P ≤ S) (hr : rounds ≤ S)
    (hcount : scopes.length ≤ 3 * n + rounds + 2)
    (hmass : HighIncidenceProgram.Prepare.mass scopes ≤ (3 * n * D + (rounds + 1) * P + 1) * k)
    (harity : ∀ row ∈ scopes, row.length ≤ (D + P + 1) * k) :
    LeafParametersProgram.magnitude
      (measuredParameterInput scopes (forwardHighMask scopes n (Nat.sqrt (L n) + 1)) m k) ≤
        10400 * S ^ 6 := by
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by decide) S
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have hND : n * D ≤ S ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hnS hD
  have hRP : (rounds + 1) * P ≤ 2 * S ^ 2 := by
    have h := Nat.mul_le_mul (show rounds + 1 ≤ 2 * S by omega) hP
    nlinarith only [h]
  have hinside : 3 * n * D + (rounds + 1) * P + 1 ≤ 6 * S ^ 2 := by nlinarith only [hND, hRP, hS, hS2]
  have hmass' : HighIncidenceProgram.Prepare.mass scopes ≤ 6 * S ^ 3 := by
    have hh := Nat.mul_le_mul hinside hkS
    nlinarith only [hmass, hh]
  have harity' : ∀ row ∈ scopes, row.length ≤ 3 * S ^ 2 := by
    intro row hrow
    have hi : D + P + 1 ≤ 3 * S := by omega
    have hh := Nat.mul_le_mul hi hkS
    have ha := harity row hrow
    nlinarith only [hh, ha]
  have htau : Nat.sqrt (L n) + 1 ≤ 19 * S := by
    have hl := Nat.log2_le_self (n + 16)
    have hs := Nat.sqrt_le_self (L n)
    unfold L at hs ⊢
    omega
  have h := raw_scope_magnitude_le scopes n m k (Nat.sqrt (L n) + 1) (20 * S ^ 3)
    hn (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun row hrow => (harity' row hrow).trans (by omega)) (by omega)
  convert h using 1
  ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
