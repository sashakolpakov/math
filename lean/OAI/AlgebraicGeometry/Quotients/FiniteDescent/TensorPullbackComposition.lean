import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackSpec
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AdjointComparisonConjugate

/-! # Tensor Pullback Composition -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackComposition.Construction.TensorPullbackMap

noncomputable section

/-! Compatibility of the tensor-power comparison with successive scheme pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem multilinear_pushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {P Q : X.Modules} {n : ℕ} (β : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap P n Q) :
    ((β.pushforward f).pushforward g).postcomp ((Scheme.Modules.pushforwardComp f g).hom.app Q) =
      (β.pushforward (f ≫ g)).precomp ((Scheme.Modules.pushforwardComp f g).hom.app P) := by
  ext U s
  rfl

theorem pullbackComp_unit (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            ((Scheme.Modules.pullback g).obj L)) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app L ≫
        (Scheme.Modules.pushforward (f ≫ g)).map ((Scheme.Modules.pullbackComp f g).inv.app L) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv L
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  simpa only [Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc] using h

theorem comparison_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (n : ℕ) :
    TensorPullbackSpec.Construction.TensorPullbackMap.comparison (f ≫ g) L n ≫ AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullbackComp f g).inv.app L) n =
      (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L n) ≫
        (Scheme.Modules.pullback f).map (TensorPullbackSpec.Construction.TensorPullbackMap.comparison g L n) ≫
          TensorPullbackSpec.Construction.TensorPullbackMap.comparison f ((Scheme.Modules.pullback g).obj L) n := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, TensorPullbackSpec.Construction.TensorPullbackMap.homEquiv_comparison,
    AdjointComparisonConjugate.Construction.AdjointComparison.homEquiv_conjugate
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      (Scheme.Modules.pullbackComp f g).inv,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  change TensorPullbackSpec.Construction.TensorPullbackMap.adjunct (f ≫ g) L n ≫ _ =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
        ((Scheme.Modules.pullback f).map (TensorPullbackSpec.Construction.TensorPullbackMap.comparison g L n) ≫
          TensorPullbackSpec.Construction.TensorPullbackMap.comparison f ((Scheme.Modules.pullback g).obj L) n)) ≫ _
  rw [Adjunction.homEquiv_naturality_left, TensorPullbackSpec.Construction.TensorPullbackMap.homEquiv_comparison,
    Adjunction.homEquiv_naturality_right, TensorPullbackSpec.Construction.TensorPullbackMap.homEquiv_comparison]
  apply AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPower_hom_ext
  rw [AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, TensorPullbackSpec.Construction.TensorPullbackMap.adjunct_spec,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_postcomp,
    AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap_spec, AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_precomp,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp]
  rw [AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, TensorPullbackSpec.Construction.TensorPullbackMap.adjunct_spec,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_postcomp,
    TensorPullbackSpec.Construction.TensorPullbackMap.adjunct_spec, AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_precomp, AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp]
  dsimp only [Functor.comp_obj]
  rw [multilinear_pushforward_comp,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp, Category.assoc, pullbackComp_unit]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackComposition.Construction.TensorPullbackMap
