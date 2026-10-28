import OAI.RepresentationTheory.Theta.Geometric.ComplementTateLattices
import OAI.RepresentationTheory.Theta.Geometric.Relative.PositionScaling
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientConstructedPosition
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.BranchLattices

/-! # Isogeny Quotient Relative Position -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsogenyQuotientRelativePosition

noncomputable section

/-! The actual complementary IsogenyQuotient isogeny has the reversed elementary
divisors in any original split target frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Pointwise

variable {E K k : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [Field k] [CharZero k] [IsAlgClosed k]
    {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    {b : Spec (.of k) ⟶ Spec (.of K)} (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s)
    (x y : D.GeometricPoint b) (c : Over.mk b ⟶ (D.correspondence t).cover)
    (hsource : c ≫ (D.correspondence t).source = x)
    (htarget : c ≫ (D.correspondence t).target = y)
    (frame : D.FiberFrame b y)
    (hf : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame (D.fiberFamily b y) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hf in
theorem c46_complement_relativePosition (v : Fin s) :
    let e := D.c46FiberIsogeny hIsogenyQuotient t x y c hsource htarget
    let f := e.multiplierComplement D.reference.polarizationType
      (D.fiberPolarizationType hg b x) (D.fiberPolarizationType hg b y) hgood.2.2.2.2
    ∃ L : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q],
      AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame f.hom (v, false) = L.val ∧
      AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) (fun i => (t.multiplierNat : ℤ) - t.val.exponent v (Fin.rev i))
        (D.framedFiberSourceLattice b y frame (v, false)) L := by
  let e := D.c46FiberIsogeny hIsogenyQuotient t x y c hsource htarget
  let sourceFrame := IsogenySourceFrame.isogenySourceFrame e frame
  have hsf := IsogenySourceFrame.isogenySourceFrame_equivariant e frame D.localCharacter hf
  obtain ⟨M, hM, hpos⟩ := D.c46Fiber_projectedRelativePosition b x sourceFrame
    hgood hg hIsogenyQuotient t y c hsource htarget hsf (Intrinsic.BranchLattices.padicTateComparisonLatticeInput q) v
  have hMt : M = D.framedFiberSourceLattice b y frame (v, false) := by
    apply Subtype.ext
    exact hM.trans (ComplementTateLattices.isogenySourceFrame_lattice e frame (v, false))
  let L₀ := D.framedFiberSourceLattice b x sourceFrame (v, false)
  refine ⟨Relative.PositionScaling.scaledRankThreeLattice q (-(t.multiplierNat : ℤ)) L₀, ?_, ?_⟩
  · rw [ComplementTateLattices.complementary_framedLattice, Relative.PositionScaling.scaledRankThreeLattice_val, zpow_neg, zpow_natCast]
    rfl
  · rw [← hMt]
    exact Relative.PositionScaling.relativePosition_complement q _ t.multiplierNat L₀ M hpos

end

end OAI.RepresentationTheory.Theta.Geometric.IsogenyQuotientRelativePosition
