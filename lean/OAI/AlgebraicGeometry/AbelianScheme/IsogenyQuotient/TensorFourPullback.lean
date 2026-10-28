import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorQuadrilinear
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorTriplePullback

/-! # Tensor Four Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorFourPullback.Construction

noncomputable section

/-! The actual tensor pullback comparison for four line sheaves,
with its formula on the four adjunction-unit inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def tensorFourPullbackMap (M N P Q : Y.Modules) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q) ⟶
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) ((Scheme.Modules.pullback f).obj P)) ((Scheme.Modules.pullback f).obj Q) :=
  Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P) (𝟙 _)

theorem tensorFourPullbackMap_isIso (M N P Q : Y.Modules)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q) :
    IsIso (tensorFourPullbackMap f M N P Q) := by
  have : IsIso (TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P) := TensorTriplePullback.Construction.tensorTriplePullbackMap_isIso f M N P hM hN hP
  have : IsIso (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q) :=
    Picard.PoincareBundle.Tensor.LinePullback.pullbackMap_isIso f _ Q (TensorTriplePullback.Construction.tensorModule_isLine (TensorTriplePullback.Construction.tensorModule_isLine hM hN) hP) hQ
  unfold tensorFourPullbackMap
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem tensorFourPullbackMap_app_unit (M N P Q : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) (q : Γ(Q, U)) :
    (tensorFourPullbackMap f M N P Q).app (f ⁻¹ᵁ U)
      ((TensorTriplePullback.Construction.linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q)).app U
        ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q).app U
          ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) q)) =
      (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))
          ((Scheme.Modules.pullback f).obj P)) ((Scheme.Modules.pullback f).obj Q)).app (f ⁻¹ᵁ U)
        ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear
          (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))
          ((Scheme.Modules.pullback f).obj P)).app (f ⁻¹ᵁ U)
            ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)).app
              (f ⁻¹ᵁ U) ((TensorTriplePullback.Construction.linePullbackUnit f M).app U m) ((TensorTriplePullback.Construction.linePullbackUnit f N).app U n))
            ((TensorTriplePullback.Construction.linePullbackUnit f P).app U p)) ((TensorTriplePullback.Construction.linePullbackUnit f Q).app U q) := by
  change (Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P) (𝟙 _)).app _
    ((Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q).app _ _) = _
  rw [TensorTriplePullback.Construction.tensorPullbackMap_app_unit, TrilinearProducts.Construction.tensorMap_app_tensor, TensorTriplePullback.Construction.tensorTriplePullbackMap_app_unit]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorFourPullback.Construction
