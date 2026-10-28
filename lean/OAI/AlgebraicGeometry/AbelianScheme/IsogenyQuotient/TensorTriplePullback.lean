import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearProducts

/-! # Tensor Triple Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorTriplePullback.Construction

noncomputable section

/-! The tensor comparison for three actual line sheaves and its
formula on sections coming from the pullback adjunction units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

abbrev linePullbackUnit (M : Y.Modules) : M ⟶
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M

theorem linePullbackUnit_natural {M N : Y.Modules} (a : M ⟶ N)
    (U : Y.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U) ((linePullbackUnit f M).app U m) =
      (linePullbackUnit f N).app U (a.app U m) :=
  (congrArg (fun h => h.app U m)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a)).symm

theorem tensorPullbackMap_app_unit (M N : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N).app (f ⁻¹ᵁ U)
      ((linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n)) =
        (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)).app
          (f ⁻¹ᵁ U) ((linePullbackUnit f M).app U m) ((linePullbackUnit f N).app U n) := by
  have h := Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap_characterization f M N
  rw [Adjunction.homEquiv_unit, Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp] at h
  exact congrArg (fun b => b.app U m n) h

theorem tensorModule_isLine {Z : Scheme.{u}} {M N : Z.Modules}
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) :
    Picard.PoincareBundle.Line.Bundles.IsLine (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) := by
  let L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z := ⟨M, hM⟩
  let K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z := ⟨N, hN⟩
  exact (L.tensor K).locallyTrivial

def tensorTriplePullbackMap (M N P : Y.Modules) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) ⟶
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))
        ((Scheme.Modules.pullback f).obj P) :=
  Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N) (𝟙 _)

theorem tensorTriplePullbackMap_isIso (M N P : Y.Modules)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) :
    IsIso (tensorTriplePullbackMap f M N P) := by
  have : IsIso (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N) := Picard.PoincareBundle.Tensor.LinePullback.pullbackMap_isIso f M N hM hN
  have : IsIso (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) :=
    Picard.PoincareBundle.Tensor.LinePullback.pullbackMap_isIso f _ P (tensorModule_isLine hM hN) hP
  unfold tensorTriplePullbackMap
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem tensorTriplePullbackMap_app_unit (M N P : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    (tensorTriplePullbackMap f M N P).app (f ⁻¹ᵁ U)
      ((linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P)).app U
        ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p)) =
      (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))
        ((Scheme.Modules.pullback f).obj P)).app (f ⁻¹ᵁ U)
          ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)).app
            (f ⁻¹ᵁ U) ((linePullbackUnit f M).app U m) ((linePullbackUnit f N).app U n))
          ((linePullbackUnit f P).app U p) := by
  change (Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N) (𝟙 _)).app _
    ((Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app _ _) = _
  rw [tensorPullbackMap_app_unit, TrilinearProducts.Construction.tensorMap_app_tensor, tensorPullbackMap_app_unit]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorTriplePullback.Construction
