import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBoundsIncidence

namespace OAI.Algorithms

/-! The numerical source parameters are bounded from the actual retained
master words in SourceReady.Input. No scalar-size premise is left separate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly

theorem sourceCaps_of_physical {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : Source.Data} {v N f S : ℕ} (h : SourceReady.Input p ps P a v N f S) :
    SourceCaps p S S := by
  have hwidth : 1 ≤ baseWidth 3 p.t := by
    have hp : 0 < baseWidth 3 p.t := by unfold baseWidth; exact Nat.mul_pos p.ht (by omega)
    omega
  have hfull : d*baseWidth 3 p.t ≤ S := by
    simpa only [h.ringWidth,p.hringWidth] using h.size 717
  refine ⟨le_rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [h.colors,List.length_replicate] using h.size 130
  · simpa only [h.nodes,List.length_replicate] using h.size 131
  · simpa only [h.offset] using h.size 139
  · exact (Nat.le_succ _).trans h.countSize
  · simpa only [h.scalarWidth] using h.size 140
  · simpa only [RowSelectionProgram.pairLength,h.powerNegative,List.length_nil,Nat.add_zero,h.power] using h.size 712
  · nlinarith
  · have hd := p.hd; nlinarith

theorem nativeSource_physical_polynomial : ∃ C e : ℕ, ∀ {r Q d : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)} {a : Source.Data} {v N f S : ℕ},
    SourceReady.Input p ps P a v N f S →
    Source.nativeSourceWorkPolynomial p S ≤ C*(S+1)^e := by
  obtain ⟨C,e,he⟩ := nativeSource_polynomial
  exact ⟨C,e,fun h => he _ _ _ (sourceCaps_of_physical h)⟩

/-- Fixed constants are chosen before all source data, caps and machine
states. The only remaining inequalities concern actual word-size caps. -/
theorem sourceAware_physical_polynomial : ∃ C e : ℕ, ∀ {r Q d : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)} {a : Source.Data} {v N f S : ℕ},
    SourceReady.Input p ps P a v N f S → ∀ n J A B Z X,
    S ≤ X → n ≤ X → J ≤ X → A ≤ X → B ≤ X → Z ≤ X →
    FactorBounds.sourceAwareSize p n J S A B Z ≤ C*(X+1)^e := by
  obtain ⟨C,e,he⟩ := nativeSource_physical_polynomial
  refine ⟨C+10,e+1,?_⟩
  intro r Q d p ps P a v N f S h n J A B Z X hS hn hJ hA hB hZ
  have hc := sourceCaps_of_physical h
  have hs := (he h).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hS 1) e))
  have hr := h.countSize.trans hS
  have hd := hc.dimension.trans hS
  have hw := hc.width.trans hS
  have hp : (X+1)^e ≤ (X+1)^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hi : X+1 ≤ (X+1)^(e+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ X+1) (show 1 ≤ e+1 by omega)
  unfold FactorBounds.sourceAwareSize
  nlinarith

theorem branch_physical_polynomial : ∃ C e : ℕ, ∀ {r Q d : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)} {a : Source.Data} {v N f S : ℕ},
    SourceReady.Input p ps P a v N f S → ∀ n J A B Z X,
    S ≤ X → n ≤ X → J ≤ X → A ≤ X → B ≤ X → Z ≤ X →
    FactorBounds.branchBound p n J S A B Z ≤ C*(X+1)^e := by
  obtain ⟨C,e,he⟩ := sourceAware_physical_polynomial
  refine ⟨275000000*C^11,e*11,?_⟩
  intro r Q d p ps P a v N f S h n J A B Z X hS hn hJ hA hB hZ
  exact (FactorBounds.branchBound_assembled p n J S A B Z C (X+1) e
    (he h n J A B Z X hS hn hJ hA hB hZ))

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms
