import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.Cech
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.DualUnitClass

/-! # Deformation Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.DeformationClass

noncomputable section

/-! A line bundle on the actual dual-number family, together with a
trivialization of its reduction, defines a class in the original
algebraic structure-sheaf H1. All affine frames are constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

def normalizedDualFrameClass {I : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤) :
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1 :=
  Regular.DualUnitClass.regularDualUnitClass X.left (Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) hs
    (LineFrameDualCech.lineFrameDualCech X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine))
    (NormalizedDual.Cech.normalizedDualFrames_cech X L e₀ s)
    (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine))

def dualLineDeformationClass : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1 :=
  normalizedDualFrameClass X L e₀ (Dual.NormalizedFrameCover.normalizedDualFrameAt X L e₀)
    (Dual.NormalizedFrameCover.normalizedDualFrameCover_base X L e₀)

theorem normalizedDualFrameClass_zero_gauge {I : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤)
    (hz : normalizedDualFrameClass X L e₀ s hs = 0) :
    ∃ g : ∀ i, (DualNumber Γ(X.left, (s i).baseOpen X L e₀))ˣ,
      (∀ i, (g i).val.fst = 1) ∧ ∀ a : Fin 2 → I,
        LineFrameDualCech.lineFrameDualCech X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine) a =
          Dual.UnitCechCoefficients.dualCechRestrict X.left.sheaf.obj
            (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).baseOpen X L e₀) a 1) (g (a 1)) /
          Dual.UnitCechCoefficients.dualCechRestrict X.left.sheaf.obj
            (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).baseOpen X L e₀) a 0) (g (a 0)) :=
  Dual.UnitCechClassification.dualUnitCechClass_zero_gauge X.left.sheaf (Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) hs
    (LineFrameDualCech.lineFrameDualCech X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine))
    (NormalizedDual.Cech.normalizedDualFrames_cech X L e₀ s)
    (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine)) hz

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.DeformationClass
