import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricOppositeLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricTargetDetermination
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteChosenFlags

/-! # Geometric Lattice Targets -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! At a fixed multiplier, the actual chosen Tate lattices determine
the geometric target of any PEL isogeny. This defines the endpoint map
used to transfer local convolution counts to geometric neighbors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} (x : D.GeometricPoint b)
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

omit [CharZero k] in
def Data.SphericalPELAlbaneseData.IsLatticeTarget (m : ℕ) (L : Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q]) (y : D.GeometricPoint b) : Prop :=
  ∃ e : PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ m),
    ∀ v, Rational.framedTateLattice frame e.isogeny.hom (v, false) = (L v).val

include hg hgeometry hf in
theorem Data.SphericalPELAlbaneseData.geometricLatticeTarget_unique (m : ℕ) (L : Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q])
    (y z : D.GeometricPoint b) (hy : D.IsLatticeTarget x frame m L y) (hz : D.IsLatticeTarget x frame m L z) : y = z := by
  obtain ⟨e, he⟩ := hy
  obtain ⟨f, hf'⟩ := hz
  apply D.geometricTarget_eq_of_preimage_eq hg hgeometry x y z e f
  apply D.preimage_eq_of_framedTateLattice_eq hg e frame hf D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2 f
  rintro ⟨v, side⟩
  cases side
  · exact (he v).trans (hf' v).symm
  · rw [D.geometricIsogeny_opposite_lattice hg hgeometry frame hf e,
      D.geometricIsogeny_opposite_lattice hg hgeometry frame hf f, he, hf']

omit [CharZero k] in
def Data.SphericalPELAlbaneseData.geometricLatticeTarget (m : ℕ) (L : Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q]) : D.GeometricPoint b :=
  if h : ∃ y, D.IsLatticeTarget x frame m L y then h.choose else x

include hg hgeometry hf in
theorem Data.SphericalPELAlbaneseData.geometricLatticeTarget_eq (m : ℕ) (L : Fin s → Duality.RankThreeLattice ℤ_[q] ℚ_[q])
    (y : D.GeometricPoint b) (hy : D.IsLatticeTarget x frame m L y) :
    D.geometricLatticeTarget x frame m L = y := by
  have h : ∃ z, D.IsLatticeTarget x frame m L z := ⟨y, hy⟩
  rw [Data.SphericalPELAlbaneseData.geometricLatticeTarget, dite_eq_left h]
  exact D.geometricLatticeTarget_unique hg hgeometry x frame hf m L h.choose y h.choose_spec hy

include hg hgeometry hf in
theorem Data.SphericalPELAlbaneseData.c46Final_geometricLatticeTarget (hIsogenyQuotient : D.RealizesIsogenyQuotient) {ts : List (Local.IntegralType s)}
    (F : D.PELFlag b x ts) :
    D.geometricLatticeTarget x frame (Data.SphericalPELAlbaneseData.flagMultiplier ts (Fin.last ts.length))
        (D.c46ChosenLattices frame hIsogenyQuotient F (Fin.last ts.length)) = F.point (Fin.last ts.length) := by
  apply D.geometricLatticeTarget_eq hg hgeometry x frame hf
  exact ⟨D.c46FlagComposites hIsogenyQuotient F (Fin.last ts.length), fun _ => rfl⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
