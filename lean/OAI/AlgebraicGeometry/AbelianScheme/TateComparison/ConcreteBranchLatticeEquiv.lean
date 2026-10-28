import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ChosenBranchInjectivity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientConstructedPosition
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricBranches
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionChoices

/-! # Concrete Branch Lattice Equiv -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteBranchLatticeEquiv.SphericalPELAlbaneseData

noncomputable section

/-! The actual chosen Tate lattices bijectively classify one-step
geometric branches in every compatible source frame. Injectivity uses
the actual kernel embedding; surjectivity follows from the checked raw
coset count for both the geometric branches and the lattice choices. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} (x : D.GeometricPoint b)
  (frame : D.FiberFrame b x) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (t : Local.IntegralType s)
  (hg : D.IsGoodCompletelySplitPrime) (hgeometry : D.HasIntegralModelGeometry)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q
    D.localCharacter frame) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

abbrev _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.BranchLatticeChoices := ∀ v : Fin s,
  {M : Duality.RankThreeLattice ℤ_[q] ℚ_[q] // Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent v)
    (D.framedFiberSourceLattice b x frame (v, false)) M}

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46BranchNextLattices (c : (D.correspondence t).Fiber x) :
    D.BranchLatticeChoices x frame t := fun v =>
  let h := D.c46Fiber_projectedRelativePosition b x frame hg hgeometry hIsogenyQuotient t
    (c.val ≫ (D.correspondence t).target) c.val c.property rfl hf hElementaryDivisors v
  ⟨h.choose, h.choose_spec.2⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46BranchNextLattices_lattice (c : (D.correspondence t).Fiber x) (v : Fin s) :
    ((D.c46BranchNextLattices x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors c v).val).val =
      D.c46ChosenBranchLattices x frame hIsogenyQuotient t c v :=
  (D.c46Fiber_projectedRelativePosition b x frame hg hgeometry hIsogenyQuotient t
    (c.val ≫ (D.correspondence t).target) c.val c.property rfl hf hElementaryDivisors v).choose_spec.1

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46BranchNextLattices_injective :
    Function.Injective (D.c46BranchNextLattices x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors) := by
  intro c d h
  apply D.c46ChosenBranchLattices_injective x frame hIsogenyQuotient t hg hgeometry hf
  funext v
  rw [← D.c46BranchNextLattices_lattice x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors c v,
    ← D.c46BranchNextLattices_lattice x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors d v, h]

variable (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)

private def branchRawLatticeCountEquiv :
    (D.correspondence t).Fiber x ≃ D.BranchLatticeChoices x frame t := by
  refine (D.geometricFiberRawCosetEquiv hg hdegree hs hgeometry b x hIsogenyQuotient t).trans
    (Equiv.piCongrRight fun v => ?_)
  simpa only [Local.IntegralType.exponentNat_cast] using
    RelativePositionChoices.rawRelativePositionEquiv q hElementaryDivisors (D.framedFiberSourceLattice b x frame (v, false))
      (t.exponentNat v)

include hdegree hs in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46BranchNextLattices_bijective :
    Function.Bijective (D.c46BranchNextLattices x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors) := by
  let e := (branchRawLatticeCountEquiv D) x frame hIsogenyQuotient t hg hgeometry hElementaryDivisors hdegree hs
  have : Finite (D.BranchLatticeChoices x frame t) := Finite.of_equiv ((D.correspondence t).Fiber x) e
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨D.c46BranchNextLattices_injective x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors, Nat.card_congr e⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46BranchLatticeEquiv :
    (D.correspondence t).Fiber x ≃ D.BranchLatticeChoices x frame t :=
  Equiv.ofBijective (D.c46BranchNextLattices x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors)
    (D.c46BranchNextLattices_bijective x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors hdegree hs)

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46BranchLatticeEquiv_lattice (c : (D.correspondence t).Fiber x) (v : Fin s) :
    ((D.c46BranchLatticeEquiv x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors hdegree hs c v).val).val =
      D.c46ChosenBranchLattices x frame hIsogenyQuotient t c v :=
  D.c46BranchNextLattices_lattice x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors c v

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteBranchLatticeEquiv.SphericalPELAlbaneseData
