import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteBranchLatticeEquiv
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyFrameTransport

/-! # Branch Frame Lattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The next lattice selected by the actual branch bijection is exactly
the source integral lattice for the next step in the transported frame. -/

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
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)

theorem Data.SphericalPELAlbaneseData.c46Branch_targetFrame_sourceLattice (c : (D.correspondence t).Fiber x) :
    (fun v => D.framedFiberSourceLattice b (c.val ≫ (D.correspondence t).target)
      ((D.c46FiberIsogeny hIsogenyQuotient t x (c.val ≫ (D.correspondence t).target)
        c.val c.property rfl).targetFrame q frame) (v, false)) =
      fun v => (D.c46BranchLatticeEquiv x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors hdegree hs c v).val := by
  funext v
  apply Subtype.ext
  rw [D.c46BranchLatticeEquiv_lattice x frame hIsogenyQuotient t hg hgeometry hf hElementaryDivisors hdegree hs c v]
  change (Rational.framedIntegralTateImage
    ((D.c46FiberIsogeny hIsogenyQuotient t x (c.val ≫ (D.correspondence t).target)
      c.val c.property rfl).targetFrame q frame)).map _ = _
  rw [PELIsogenies.PELIsogeny.targetFrame_integral]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
