import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCostRuntime
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCostParameters

namespace OAI.Algorithms

/-! Full numeric selector envelope. Every failed candidate and every marked
count is retained. All physical input-word lengths are bounded by the supplied
measured source size W, with no canonical-width replacement. -/
namespace SubexponentialSAT.SqrtLog.Execution.SelectorCost
open Statement Filter CostAssembly Asymptotic
open scoped Topology

 theorem eventually_history_bound {Cq Aq : ℝ} (hCq : 1 ≤ Cq) (hAq : 0 ≤ Aq)
    (dq q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B W : ℕ, ∀ count depth rounds : List Bool,
      ∀ Q mass countSteps countBits : ℕ,
      0 < m → m ≤ n*B → B ≤ L n^q →
      CounterPrograms.value count = 3*m →
      CounterPrograms.value depth = SparseCode.distanceDenom m B →
      CounterPrograms.value rounds = HashSelect.loopCap n m →
      count.length ≤ W → depth.length ≤ W → rounds.length ≤ W →
      Q ≤ Nat.ceil (runtimeBound Cq Aq dq W n) →
      mass ≤ m*Q+LeafOuterNative.overhead W m (LeafParametersProgram.precision n m) (Q+1)+64 →
      countSteps ≤ 5000*(W+Q+1) → countBits ≤ Q+1 →
      Hash.budget count depth rounds (LeafParametersProgram.precision n m)
        (CounterPrograms.value depth*count.length) mass + countSteps + 5*countBits + 11 ≤
      Nat.floor (runtimeBound (3000000*4^8*Cq) (16+Aq) (8+dq) W n) := by
  filter_upwards [eventually_commonHeight q,eventually_commonHeight_bounds q]
    with n hreal hnat m B W count depth rounds Q mass countSteps countBits hm hmn hB
      hc hd hr hcl hdl hrl hQ hmass hsteps hbits
  let H := commonHeight W n m B
  obtain ⟨hW,hmH,hcH,hdH,hrH,hpH,hpayload,hfH⟩ := hnat m B W hm hmn hB
  have hh := history_le count depth rounds (LeafParametersProgram.precision n m)
    (CounterPrograms.value depth*count.length) W m H Q mass countSteps countBits
    (by rw [hc]; omega) (by simpa only [hc] using hcH) (by simpa only [hd] using hdH)
    (by simpa only [hr] using hrH) (hcl.trans hW) (hdl.trans hW) (hrl.trans hW)
    (by simpa only [hc,hd] using hfH) hpH
    (by rw [hd]; exact (Nat.mul_le_mul_left _ hcl).trans hpayload) hW hmH hmass hsteps hbits
  have hsource : (W:ℝ)+1 ≤ runtimeBound 1 0 1 W n := by simp [runtimeBound]
  have hfinal := envelope_runtime (Ch:=4) (Ah:=2) (Cs:=1) (As:=0) (Cq:=Cq) (Aq:=Aq)
    (by norm_num) (by norm_num) hCq hAq 1 1 dq W n H W Q
    (Hash.budget count depth rounds (LeafParametersProgram.precision n m)
      (CounterPrograms.value depth*count.length) mass + countSteps + 5*countBits + 11)
    (hreal m B W hmn hB) hsource hQ hh
  apply (Nat.le_floor_iff (by unfold runtimeBound; positivity)).2
  simpa only [Nat.one_mul, one_mul, one_pow, mul_one, mul_zero, add_zero,
    show (8:ℝ)*2=16 by norm_num] using hfinal

/-- Real-valued form for the final machine runtime composition. -/
theorem eventually_history_runtime {Cq Aq : ℝ} (hCq : 1 ≤ Cq) (hAq : 0 ≤ Aq)
    (dq q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B W : ℕ, ∀ count depth rounds : List Bool,
      ∀ Q mass countSteps countBits : ℕ,
      0 < m → m ≤ n*B → B ≤ L n^q →
      CounterPrograms.value count = 3*m →
      CounterPrograms.value depth = SparseCode.distanceDenom m B →
      CounterPrograms.value rounds = HashSelect.loopCap n m →
      count.length ≤ W → depth.length ≤ W → rounds.length ≤ W →
      Q ≤ Nat.ceil (runtimeBound Cq Aq dq W n) →
      mass ≤ m*Q+LeafOuterNative.overhead W m (LeafParametersProgram.precision n m) (Q+1)+64 →
      countSteps ≤ 5000*(W+Q+1) → countBits ≤ Q+1 →
      ((Hash.budget count depth rounds (LeafParametersProgram.precision n m)
        (CounterPrograms.value depth*count.length) mass + countSteps + 5*countBits + 11:ℕ):ℝ) ≤
      runtimeBound (3000000*4^8*Cq) (16+Aq) (8+dq) W n := by
  filter_upwards [eventually_history_bound hCq hAq dq q] with n hn
  intro m B W count depth rounds Q mass countSteps countBits hm hmn hB hc hd hr hcl hdl hrl hQ hmass hs hb
  have hh := hn m B W count depth rounds Q mass countSteps countBits hm hmn hB hc hd hr
    hcl hdl hrl hQ hmass hs hb
  exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (by unfold runtimeBound; positivity))

end SubexponentialSAT.SqrtLog.Execution.SelectorCost

end OAI.Algorithms
