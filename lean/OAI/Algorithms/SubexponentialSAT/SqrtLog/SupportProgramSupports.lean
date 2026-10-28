import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeMaskDecode

namespace OAI.Algorithms

/-! Exact finite-set interpretation of the masks emitted by the fixed support
program. No ordering assumption is needed by the moment consumer. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree SubexponentialSAT.BitProgram Steps

/-- Decode only the already generated rows; this does not enumerate a powerset. -/
def supports (n : ℕ) (rows : List (List Bool)) : List (Finset (Fin n)) :=
  rows.map (decodeMask n)

theorem supports_nodup (n J : ℕ) (rows : List (List Bool)) (h : Correct n J rows) :
    (supports n rows).Nodup := by
  apply List.Nodup.map_on _ h.1
  intro x hx y hy he
  have hex := encodeMask_decodeMask n x ((h.2 x).mp hx).1
  have hey := encodeMask_decodeMask n y ((h.2 y).mp hy).1
  have hh := congrArg encodeMask he
  simpa only [hex, hey] using hh

@[simp] theorem mem_supports (n J : ℕ) (rows : List (List Bool))
    (h : Correct n J rows) (s : Finset (Fin n)) :
    s ∈ supports n rows ↔ s.card < J := by
  constructor
  · intro hs
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hs
    rw [decodeMask_card n xs ((h.2 xs).mp hxs).1]
    exact ((h.2 xs).mp hxs).2
  · intro hs
    apply List.mem_map.mpr
    refine ⟨encodeMask s, (h.2 _).mpr ?_, decodeMask_encodeMask s⟩
    exact ⟨encodeMask_length s, by simpa using hs⟩

theorem supports_length (n J : ℕ) (rows : List (List Bool)) (h : Correct n J rows) :
    (supports n rows).length = count n J := by
  simpa only [supports,List.length_map] using correct_length n J rows h

theorem supports_encode (n J : ℕ) (rows : List (List Bool)) (h : Correct n J rows) :
    (supports n rows).map encodeMask = rows := by
  unfold supports
  rw [List.map_map]
  have hh : rows.map (encodeMask ∘ decodeMask n) = rows.map id := by
    apply List.map_congr_left
    intro xs hxs
    exact encodeMask_decodeMask n xs ((h.2 xs).mp hxs).1
  simpa using hh

/-- The actual primitive execution yields exactly M_J distinct support sets,
each with cardinality less than J, and emits their masks in the same order. -/
theorem primitive_supports (depth budget : List Bool) (hJ : 0 < budget.length) :
    ∃ (b : Data) (ss : List (Finset (Fin depth.length))),
      ss.Nodup ∧ (∀ s, s ∈ ss ↔ s.card < budget.length) ∧
      ss.length = count depth.length budget.length ∧
      b.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords (ss.map encodeMask) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          (4000 * (depth.length+1) * (depth.length+budget.length+1) * count depth.length budget.length))
        (primitiveCfg program ((inputState depth budget).withPC (some program.entry)))
        (primitiveCfg program (b.withPC none)) := by
  obtain ⟨b,rows,h,hout,htrace⟩ := primitive_runsIn depth budget hJ
  refine ⟨b,supports depth.length rows,supports_nodup _ _ _ h,
    fun s => mem_supports _ _ _ h s,supports_length _ _ _ h,?_,htrace⟩
  rw [supports_encode _ _ _ h]
  exact hout

end SubexponentialSAT.SqrtLog.SupportProgram

end OAI.Algorithms
