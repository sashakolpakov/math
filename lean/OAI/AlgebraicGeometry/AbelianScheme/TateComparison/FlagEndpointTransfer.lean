import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFlagEndpoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LinearFlagEndpoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricLatticeTargets
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RecursiveFlagLattices

/-! # Flag Endpoint Transfer -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual flag bijection transports terminal lattice multiplicities
to the actual geometric endpoints at the cumulative multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} (x : D.GeometricPoint b)
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors hf in
theorem Data.SphericalPELAlbaneseData.geometricFlagEndpoints_eq_lattice_map (ts : List (Local.IntegralType s)) :
    D.geometricFlagEndpoints b x ts =
      (LinearFlagEndpoints.linearFlagEndpoints s q (fun v => D.framedFiberSourceLattice b x frame (v, false)) ts).map
        (D.geometricLatticeTarget x frame (Data.SphericalPELAlbaneseData.flagMultiplier ts (Fin.last ts.length))) := by
  let L₀ := fun v => D.framedFiberSourceLattice b x frame (v, false)
  let : Fintype (D.PELFlag b x ts) := Fintype.ofFinite _
  let : Fintype (Duality.LinearBlockFlags (q : ℤ_[q]) L₀ ts) := Fintype.ofFinite _
  let e := Equiv.ofBijective (D.c46ChosenFlag (ts := ts) frame hIsogenyQuotient hg hgeometry hf hElementaryDivisors)
    (D.c46ChosenFlag_bijective hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors ts x frame hf)
  change (Finset.univ : Finset (D.PELFlag b x ts)).val.map _ =
    ((Finset.univ : Finset (Duality.LinearBlockFlags (q : ℤ_[q]) L₀ ts)).val.map _).map _
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro F _
  exact (D.c46Final_geometricLatticeTarget hg hgeometry x frame hf hIsogenyQuotient F).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
