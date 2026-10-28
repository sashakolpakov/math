import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PullbackTensorFrame
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames

/-! # Open Frame Agreement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.OpenFrameAgreement

noncomputable section

/-! The actual pullback tensor frame converts to the canonical
native open tensor frame through the original restriction comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

local instance tensorOpenFrameMonoidal (X : Scheme.{0}) : MonoidalCategory X.Modules :=
  SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance tensorOpenFramePullbackMonoidal {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f

theorem monoidalOpenFrame_pullback {X : Scheme.{0}} (M N : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback U.ι).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso U.ι M N ≪≫
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e) ⊗ᵢ
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫ d)) ≪≫ SheafCohomology.Projective.TensorSections.unitObjTensorIso U.toScheme =
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (M ⊗ N) ≪≫ Pullback.TensorFrame.pullbackTensorFrame U.ι M N e d := by
  have h := SheafCohomology.Projective.PullbackFrameComposition.restrictMonoidalTensorTrivialization_eq_pullback U.ι M N
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫ d)
  have hc := congrArg₂ (fun e' d' =>
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (M ⊗ N) ≪≫ Pullback.TensorFrame.pullbackTensorFrame U.ι M N e' d')
    (Iso.symm_self_id_assoc ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) e)
    (Iso.symm_self_id_assoc ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N) d)
  exact h.trans hc

theorem algebraicOpenFrame_pullback {X : Scheme.{0}} (M N : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback U.ι).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫
      PullbackTensorFrame.algebraicPullbackTensorFrame U.ι M N e d =
    RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame M N U
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e)
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫ d) := by
  have h₁ := ReducedFrame.transportedFrame_precomp (Scheme.Modules.restrictFunctorIsoPullback U.ι)
    (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M N).symm (Pullback.TensorFrame.pullbackTensorFrame U.ι M N e d)
  have h₂ := congrArg (fun q => (Scheme.Modules.restrictFunctor U.ι).mapIso
    (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M N).symm ≪≫ q) (monoidalOpenFrame_pullback M N U e d).symm
  exact h₁.trans h₂

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.OpenFrameAgreement
