import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricOppositeLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricWeilIntegralFrame
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RecursiveFlagLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricBlockDetermination

/-! # Polarized Flag Realizations -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Construct the full polarized flag realization from actual IsogenyQuotient
isogenies, their canonical Weil pairing, and the recursive lattice
bijection. The one source frame and pairing work for every word. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

section Fiber
variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} {x : D.GeometricPoint b}
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
  {ts : List (Local.IntegralType s)}

theorem Data.SphericalPELAlbaneseData.c46ChosenFlag_realizes (F : D.PELFlag b x ts) :
    D.RealizesLinearFlag hIsogenyQuotient frame
      (D.framedOppositePairing (D.fiberFamily b x) _ frame
        (D.geometricRationalWeilPairing hg hgeometry b x))
      (fun v => D.framedFiberSourceLattice b x frame (v, false)) F
      (D.c46ChosenFlag frame hIsogenyQuotient hg hgeometry hf hElementaryDivisors F)
      (D.finalComposite (D.c46FlagComposites hIsogenyQuotient F)) := by
  refine ⟨D.c46FlagComposites hIsogenyQuotient F, D.c46FlagSteps hIsogenyQuotient F, ?_, rfl, ?_⟩
  · exact D.c46FlagComposites_isCompositeSystem hIsogenyQuotient F
  · intro j v
    exact ⟨rfl, D.geometricComposite_opposite_lattice hg hgeometry frame hf _ j v⟩

include hdegree hs hf hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.polarizedFlags_in_frame :
    ∃ (flags : D.PELFlag b x ts ≃ Duality.LinearBlockFlags (q : ℤ_[q])
        (fun v => D.framedFiberSourceLattice b x frame (v, false)) ts)
      (composite : Duality.LinearBlockFlags (q : ℤ_[q])
        (fun v => D.framedFiberSourceLattice b x frame (v, false)) ts → D.CompositeDatum x ts),
      (∀ F, D.RealizesLinearFlag hIsogenyQuotient frame
        (D.framedOppositePairing (D.fiberFamily b x) _ frame
          (D.geometricRationalWeilPairing hg hgeometry b x))
        (fun v => D.framedFiberSourceLattice b x frame (v, false)) F (flags F) (composite (flags F))) ∧
      ∀ L L', L.val (Fin.last ts.length) = L'.val (Fin.last ts.length) → composite L = composite L' := by
  let flags := Equiv.ofBijective (D.c46ChosenFlag (ts := ts) frame hIsogenyQuotient hg hgeometry hf hElementaryDivisors)
    (D.c46ChosenFlag_bijective hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf)
  let composite := fun L => D.finalComposite (D.c46FlagComposites hIsogenyQuotient (flags.symm L))
  have hr (L) : D.RealizesLinearFlag hIsogenyQuotient frame
      (D.framedOppositePairing (D.fiberFamily b x) _ frame
        (D.geometricRationalWeilPairing hg hgeometry b x))
      (fun v => D.framedFiberSourceLattice b x frame (v, false)) (flags.symm L) L (composite L) := by
    have h := D.c46ChosenFlag_realizes hg hgeometry hIsogenyQuotient hElementaryDivisors frame hf (flags.symm L)
    change D.RealizesLinearFlag hIsogenyQuotient frame _ _ (flags.symm L) (flags (flags.symm L)) (composite L) at h
    rw [flags.apply_symm_apply] at h
    exact h
  refine ⟨flags, composite, ?_, ?_⟩
  · intro F
    have h := hr (flags F)
    rw [flags.symm_apply_apply] at h
    exact h
  · intro L L' hL
    exact D.realizedFlag_composite_eq_of_terminal_eq hg hgeometry frame hf hIsogenyQuotient _ _ (hr L) (hr L') hL

end Fiber

include hg hdegree hs hgeometry hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.hasPolarizedFlagRealizations : D.HasPolarizedFlagRealizations hIsogenyQuotient := by
  intro k _ _ b x
  have := FiberLattices.charZero_of_field_spec_map b
  let frame := D.geometricSplitFrame hg hdegree hs hgeometry b x
  have hf := D.geometricSplitFrame_equivariant hg hdegree hs hgeometry b x
  refine ⟨frame, D.framedOppositePairing (D.fiberFamily b x) _ frame
    (D.geometricRationalWeilPairing hg hgeometry b x),
    (fun v => D.framedFiberSourceLattice b x frame (v, false)), ?_, ?_, ?_⟩
  · exact D.geometricWeilOppositePairing_nondegenerate hg hgeometry b x frame hf
  · exact D.geometricWeil_isIntegralSplitFrame hg hgeometry b x frame hf
  · intro ts
    exact D.polarizedFlags_in_frame hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors frame hf

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
