import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

/-! # Line Frame Dual Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameDualCech

noncomputable section

/-! Actual affine module-sheaf frames on the dual-number family give
an actual multiplicative Cech cocycle in the reduced coefficient rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    {M : (LieRanks.dualNumberTest ℂ ⊗ X).left.Modules} {I : Type} (s : I → LineFrameAtlas.LocalLineFrame M)
    (hs : ∀ i, IsAffineOpen (s i).domain)

def lineFrameDualCech : Dual.UnitCechCoefficients.DualUnitCechCoefficients X.left.sheaf.obj
    (Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) :=
  fun a => Units.map (Dual.CechCoefficient.dualCechSectionCoefficientEquiv X (fun i => (s i).domain) hs a).toMonoidHom
    ((s (a 0)).transition (s (a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1))

theorem lineFrameDualCech_cocycle [LocallyOfFiniteType X.hom] [IsReduced X.left] :
    Dual.UnitCechCoefficients.DualUnitCechCocycle X.left.sheaf.obj (Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain))
      (lineFrameDualCech X s hs) := by
  intro a
  dsimp only [lineFrameDualCech]
  rw [← Dual.CechCoefficient.dualCechUnitCoefficient_precomp, ← Dual.CechCoefficient.dualCechUnitCoefficient_precomp,
    ← Dual.CechCoefficient.dualCechUnitCoefficient_precomp]
  rw [LineFrameAtlas.LocalLineFrame.transition_restrict, LineFrameAtlas.LocalLineFrame.transition_restrict,
    LineFrameAtlas.LocalLineFrame.transition_restrict]
  change Units.map (Dual.CechCoefficient.dualCechSectionCoefficientEquiv X (fun i => (s i).domain) hs a).toMonoidHom
      ((s (a 1)).transition (s (a 2)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a) _ _) *
    Units.map (Dual.CechCoefficient.dualCechSectionCoefficientEquiv X (fun i => (s i).domain) hs a).toMonoidHom
      ((s (a 0)).transition (s (a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a) _ _) =
    Units.map (Dual.CechCoefficient.dualCechSectionCoefficientEquiv X (fun i => (s i).domain) hs a).toMonoidHom
      ((s (a 0)).transition (s (a 2)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a) _ _)
  rw [← map_mul, mul_comm]
  exact congrArg (Units.map (Dual.CechCoefficient.dualCechSectionCoefficientEquiv X (fun i => (s i).domain) hs a).toMonoidHom)
    ((s (a 0)).transition_cocycle (s (a 1)) (s (a 2))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 2))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameDualCech
