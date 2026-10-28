import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorObj
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf

/-! # Tensor Module Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.TensorModulePullback

noncomputable section

/-! The general sheafified-tensor pullback comparison applies to the exact
tensor module in the native Poincare formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def tensorModulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  Classical.choice (AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorObj.Scheme.Modules.nonempty_pullback_tensorObj f M N)

end

end OAI.RepresentationTheory.Theta.Geometric.TensorModulePullback
