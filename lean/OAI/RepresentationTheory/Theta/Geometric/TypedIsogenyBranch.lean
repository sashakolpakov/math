import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteBranchLatticeEquiv
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricLatticeTargets

/-! # Typed Isogeny Branch -/

namespace OAI.RepresentationTheory.Theta.Geometric.TypedIsogenyBranch

noncomputable section

/-! An actual marked polarized isogeny of the prescribed chosen lattice
type occurs in the original correspondence with its literal moduli target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem exists_original_branch_of_typed_isogeny
    {E K k : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [Field k] [CharZero k] [IsAlgClosed k]
    {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hElementaryDivisors : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) {b : Spec (.of k) ⟶ Spec (.of K)}
    (x y : D.GeometricPoint b) (frame : D.FiberFrame b x)
    (hf : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s) (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ t.multiplierNat))
    (hpos : ∀ v, ∃ L : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q],
      AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame e.isogeny.hom (v, false) = L.val ∧
      AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent v)
        (D.framedFiberSourceLattice b x frame (v, false)) L) :
    ∃ c : (D.correspondence t).Fiber x, c.val ≫ (D.correspondence t).target = y := by
  classical
  choose L hL htype using hpos
  let choices : D.BranchLatticeChoices x frame t := fun v => ⟨L v, htype v⟩
  let β := D.c46BranchLatticeEquiv x frame hIsogenyQuotient t hq hg hf hElementaryDivisors hdegree hs
  let c := β.symm choices
  refine ⟨c, ?_⟩
  apply D.geometricLatticeTarget_unique hq hg x frame hf t.multiplierNat L
  · refine ⟨D.c46FiberIsogeny hIsogenyQuotient t x (c.val ≫ (D.correspondence t).target) c.val c.property rfl, ?_⟩
    intro v
    have he := congrArg (fun F : D.BranchLatticeChoices x frame t => ((F v).val).val)
      (β.apply_symm_apply choices)
    rw [D.c46BranchLatticeEquiv_lattice x frame hIsogenyQuotient t hq hg hf hElementaryDivisors hdegree hs] at he
    exact he
  · exact ⟨e, hL⟩

end

end OAI.RepresentationTheory.Theta.Geometric.TypedIsogenyBranch
