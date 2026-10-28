import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramNative

namespace OAI.Algorithms

/-! The controller's changing ports and the preserved arithmetic context. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT

def controllerPorts : List (Fin 320) := [208,213,218,257,258,259,260,261,262,263]

def Frame (base s : Store) : Prop := ∀i,i∉controllerPorts → s i=base i

theorem Frame.refl (s : Store) : Frame s s := fun _ _ => rfl

theorem Frame.update {base s : Store} (h : Frame base s) (i : Fin 320) (v : List Bool)
    (hi : i∈controllerPorts) : Frame base (Function.update s i v) := by
  intro j hj
  rw [Function.update_of_ne (by intro he; subst j; exact hj hi)]
  exact h j hj

theorem controllerPorts_lower {i : Fin 320} (hi : i∈controllerPorts) : 208 ≤ i.val := by
  simp only [controllerPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def scratchPorts : List (Fin 320) := [205,219,220,222,240,241,244,245,246,270,271]

structure Ready (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (s : Store) : Prop where
  native : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) (s ∘ low)
  zero : s 104=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  one : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  minus : s 211=RingProgram.flat minusOne
  exponent : (s 209).length=3^d-2
  precision : (s 212).length=t
  scratch : ∀i∈scratchPorts,s i=[]

theorem Ready.frame {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {base s : Store} (h : Ready t a M cache minusOne base)
    (hf : Frame base s) : Ready t a M cache minusOne s := by
  have hn := h.native.frame (s := s ∘ low) (by
    intro i hi
    apply hf (low i)
    intro hh
    have := controllerPorts_lower hh
    change 208 ≤ i.val at this
    omega)
  refine ⟨hn,?_,?_,?_,?_,?_,?_⟩
  · exact (hf 104 (by decide)).trans h.zero
  · exact (hf 207 (by decide)).trans h.one
  · exact (hf 211 (by decide)).trans h.minus
  · rw [hf 209 (by decide)]; exact h.exponent
  · rw [hf 212 (by decide)]; exact h.precision
  · intro i hi
    rw [hf i (by
      simp only [scratchPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact h.scratch i hi

theorem Ready.width {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {s : Store} (h : Ready t a M cache minusOne s) :
    (s 104).length=d*SubexpLiftRing.baseWidth 3 t := by
  rw [h.zero,RingProgram.flat_length]

theorem Ready.inverse_run {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {s : Store} (h : Ready t a M cache minusOne s)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (x y : Coeff t d)
    (hx : s 213=RingProgram.flat x) (hy : s 218=RingProgram.flat y) (hr : s 208=[]) :
    Runs inverseCommand (inverseBudget t d) s
      (Function.update s 208 (RingProgram.flat (differenceValue t a M cache minusOne x y))) := by
  apply inverseCommand_run t a M cache hz s h.native x y minusOne hx hy h.zero h.one h.minus h.exponent h.precision
  intro i hi
  simp only [CRTLocalProgram.NativeInverse.work,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hr | exact h.scratch _ (by decide)

theorem Ready.negative_run {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {s : Store} (h : Ready t a M cache minusOne s)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (x : Coeff t d)
    (hx : s 213=RingProgram.flat x) (hr : s 208=[]) :
    Runs negativeCommand (negativeBudget t d) s
      (Function.update s 208 (RingProgram.flat (negativeValue t a M cache minusOne x))) := by
  apply negativeCommand_run t a M cache hz s h.native x minusOne hx h.minus
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hr | exact h.scratch _ (by decide)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
