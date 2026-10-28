import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Tensor Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorExactness

noncomputable section

/-! Tensoring with an actual line bundle preserves short exact sequences of module sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem lineBundleTensor_shortExact {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (TensorEquivalence.lineBundleTensorEquivalence L).functor).ShortExact :=
  hS.map_of_exact (TensorEquivalence.lineBundleTensorEquivalence L).functor

theorem lineBundleRightTensor_shortExact {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (TensorEquivalence.lineBundleRightTensorEquivalence L).functor).ShortExact :=
  hS.map_of_exact (TensorEquivalence.lineBundleRightTensorEquivalence L).functor

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorExactness
