import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedOpenFrameConverse
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame

/-! # Pullback Tensor Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PullbackTensorFrame

noncomputable section

/-! The canonical tensor frame applies to the original HilbertConstruction tensor
sheaf through its proved isomorphism with the native monoidal tensor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

local instance algebraicTensorFrameMonoidal (X : Scheme.{0}) : MonoidalCategory X.Modules :=
  SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance algebraicTensorFramePullbackMonoidal {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f

def algebraicPullbackTensorFrame {X Y : Scheme.{0}} (f : X ⟶ Y) (M N : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)
    (d : (Scheme.Modules.pullback f).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    (Scheme.Modules.pullback f).obj (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X :=
  (Scheme.Modules.pullback f).mapIso (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M N).symm ≪≫
    Pullback.TensorFrame.pullbackTensorFrame f M N e d

theorem reducedOpenFrame_algebraic_tensor {X Y : Scheme.{0}} (r : X ⟶ Y) (U : Y.Opens)
    {M N : Y.Modules} (e₀ : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)
    (d₀ : (Scheme.Modules.pullback r).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback U.ι).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (he : Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = ReducedFrame.reducedOpenFrame r e₀ U)
    (hd : Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) d = ReducedFrame.reducedOpenFrame r d₀ U) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) (algebraicPullbackTensorFrame U.ι M N e d) =
      ReducedFrame.reducedOpenFrame r (algebraicPullbackTensorFrame r M N e₀ d₀) U := by
  have h₁ := ReducedFrame.pullbackFrame_precomp (r ∣_ U)
    ((Scheme.Modules.pullback U.ι).mapIso (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M N).symm) (Pullback.TensorFrame.pullbackTensorFrame U.ι M N e d)
  have h₂ := congrArg (fun q => (Scheme.Modules.pullback (r ∣_ U)).mapIso
    ((Scheme.Modules.pullback U.ι).mapIso (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M N).symm) ≪≫ q)
      (ReducedOpenFrameConverse.reducedOpenFrame_tensor r U e₀ d₀ e d he hd)
  exact h₁.trans (h₂.trans
    (ReducedFrame.reducedOpenFrame_precomp r (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M N).symm (Pullback.TensorFrame.pullbackTensorFrame r M N e₀ d₀) U).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PullbackTensorFrame
