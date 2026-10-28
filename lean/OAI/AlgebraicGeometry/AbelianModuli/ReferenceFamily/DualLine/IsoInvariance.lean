import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.FrameIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.FrameIndependence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameIsoTransitions

/-! # Iso Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.IsoInvariance

noncomputable section

/-! Transport through an actual line-sheaf isomorphism preserves
the original algebraic deformation class, with the transported reduction frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L K : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) (q : K.sheaf ≅ L.sheaf)

theorem normalizedDualFrame_precomp_transition (a b : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (ha : U ≤ a.domain) (hb : U ≤ b.domain) :
    ((a.precomp X L K e₀ q).localFrame X K
      ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).mapIso q ≪≫ e₀)).transition
      ((b.precomp X L K e₀ q).localFrame X K
        ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).mapIso q ≪≫ e₀)) U ha hb =
      (a.localFrame X L e₀).transition (b.localFrame X L e₀) U ha hb := by
  exact Pullback.FrameIsoTransitions.pullbackLocalFrame_precomp_transition q a.domain b.domain U ha hb a.frame b.frame

variable [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

theorem normalizedDualFrameClass_precomp {I : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤) :
    DeformationClass.normalizedDualFrameClass X K ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).mapIso q ≪≫ e₀)
      (fun i => (s i).precomp X L K e₀ q) hs = DeformationClass.normalizedDualFrameClass X L e₀ s hs := by
  apply Cech.Add.cechSheafClass_congr (fun i => (s i).baseOpen X L e₀) (Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf) hs 0
  funext a
  exact congrArg (fun u => (Units.map
    (Dual.CechCoefficient.dualCechSectionCoefficientEquiv X (fun i => (s i).domain) (fun i => (s i).affine) a).toMonoidHom u).val.snd)
    (normalizedDualFrame_precomp_transition X L K e₀ q (s (a 0)) (s (a 1))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1))

theorem dualLineDeformationClass_iso :
    DeformationClass.dualLineDeformationClass X K ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).mapIso q ≪≫ e₀) =
      DeformationClass.dualLineDeformationClass X L e₀ := by
  exact (FrameIndependence.dualLineDeformationClass_eq_frames X K
    ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).mapIso q ≪≫ e₀)
    (fun x => (Dual.NormalizedFrameCover.normalizedDualFrameAt X L e₀ x).precomp X L K e₀ q)
    (Dual.NormalizedFrameCover.normalizedDualFrameCover_base X L e₀)).trans
      (normalizedDualFrameClass_precomp X L K e₀ q (Dual.NormalizedFrameCover.normalizedDualFrameAt X L e₀)
        (Dual.NormalizedFrameCover.normalizedDualFrameCover_base X L e₀))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.IsoInvariance
