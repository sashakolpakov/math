import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackLeftUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Tensor Module Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorModulePullback

noncomputable section

/-! Tensoring an arbitrary module sheaf with a line bundle commutes with arbitrary scheme pullback. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

theorem tensorPullbackComparison_isIso_of_leftTrivial (f : X ⟶ Y)
    {M : Y.Modules} (e : M ≅ Line.Bundles.structureModule Y) (P : Y.Modules) :
    IsIso (Tensor.PullbackComparison.tensorPullbackComparison f M P) := by
  have := Tensor.PullbackLeftUnit.tensorPullbackComparison_leftUnit_isIso f P
  have h : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f M P ≫
      Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullback f).map e.hom)
        ((Scheme.Modules.pullback f).map (𝟙 P))) := by
    rw [← Tensor.PullbackComparison.tensorPullbackComparison_natural]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

theorem lineBundle_tensorModulePullbackComparison_isIso (f : X ⟶ Y)
    (L : Line.Bundles.LineBundle Y) (M : Y.Modules) :
    IsIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial (f x)
  have hU : IsIso (Tensor.PullbackComparison.tensorPullbackComparison (f ∣_ U)
      ((Scheme.Modules.pullback U.ι).obj L.sheaf)
      ((Scheme.Modules.pullback U.ι).obj M)) :=
    tensorPullbackComparison_isIso_of_leftTrivial (f ∣_ U) e _
  have hc : IsIso (Tensor.PullbackComparison.tensorPullbackComparison ((f ∣_ U) ≫ U.ι) L.sheaf M) :=
    (TensorBaseChange.tensorPullbackComparison_comp_isIso_iff (f ∣_ U) U.ι L.sheaf M).mp
      ((Scheme.Modules.pullback (f ∣_ U)).map_isIso _)
  have hc' : IsIso (Tensor.PullbackComparison.tensorPullbackComparison ((f ⁻¹ᵁ U).ι ≫ f) L.sheaf M) := by
    rw [← morphismRestrict_ι f U]
    exact hc
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  exact (TensorBaseChange.tensorPullbackComparison_comp_isIso_iff (f ⁻¹ᵁ U).ι f L.sheaf M).mpr hc'

def lineBundleTensorModulePullbackIso (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule L.sheaf M) ≅
      Tensor.ProductSheaf.tensorModule (L.pullback f).sheaf ((Scheme.Modules.pullback f).obj M) :=
  @asIso X.Modules _ _ _ (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M)
    (lineBundle_tensorModulePullbackComparison_isIso f L M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorModulePullback
