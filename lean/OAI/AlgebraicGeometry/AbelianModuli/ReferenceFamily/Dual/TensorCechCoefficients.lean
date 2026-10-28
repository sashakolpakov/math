import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameDualCech
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.TensorTransition
import OAI.RepresentationTheory.Theta.Geometric.OpenFramesFactored

/-! # Tensor Cech Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCechCoefficients

noncomputable section

section

/-! The actual dual-number coefficient cocycle of tensor pullback
frames is the product of the two coefficient cocycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

def localFrameFromPullback {X : Scheme.{0}} {M : X.Modules} (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) : LineFrameAtlas.LocalLineFrame M :=
  ⟨U, (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e⟩

theorem lineFrameDualCech_tensor (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (M N : (LieRanks.dualNumberTest ℂ ⊗ X).left.Modules) {I : Type}
    (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (U i).toScheme)
    (d : ∀ i, (Scheme.Modules.pullback (U i).ι).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (U i).toScheme) (a : Fin 2 → I) :
    LineFrameDualCech.lineFrameDualCech X (fun i => localFrameFromPullback (U i)
      (PullbackTensorFrame.algebraicPullbackTensorFrame (U i).ι M N (e i) (d i))) hU a =
    (show (DualNumber Γ(X.left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover X U) a))ˣ from
      LineFrameDualCech.lineFrameDualCech X (fun i => localFrameFromPullback (U i) (e i)) hU a) *
    (show (DualNumber Γ(X.left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover X U) a))ˣ from
      LineFrameDualCech.lineFrameDualCech X (fun i => localFrameFromPullback (U i) (d i)) hU a) := by
  have h := Pullback.TensorTransition.algebraicPullbackTensorFrame_transition M N (U (a 0)) (U (a 1))
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)
    (e (a 0)) (e (a 1)) (d (a 0)) (d (a 1))
  exact (congrArg (Units.map (CechCoefficient.dualCechSectionCoefficientEquiv X U hU a).toMonoidHom) h).trans
    (map_mul (Units.map (CechCoefficient.dualCechSectionCoefficientEquiv X U hU a).toMonoidHom) _ _)

end

/-! Restricting an actual pullback frame agrees with the native
factored frame through the original open restriction comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def restrictPullbackFrame {X : Scheme.{0}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    (Scheme.Modules.pullback V.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app M ≪≫
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e)

theorem restrictPullbackFrame_factored {X : Scheme.{0}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    restrictPullbackFrame M h e =
      (Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app M ≪≫ RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame (X.homOfLE h) U.ι e := by
  have h₁ := RepresentationTheory.Theta.Geometric.OpenFramesFactored.restrictOpenFrame_as_factored M h ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e)
  have h₂ := congrArg (fun q => (Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app M ≪≫
    RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame (X.homOfLE h) U.ι q)
      (Iso.symm_self_id_assoc ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) e)
  exact h₁.trans h₂

theorem restrictPullbackFrame_open {X : Scheme.{0}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫ restrictPullbackFrame M h e =
      SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e) :=
  Iso.self_symm_id_assoc _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCechCoefficients
