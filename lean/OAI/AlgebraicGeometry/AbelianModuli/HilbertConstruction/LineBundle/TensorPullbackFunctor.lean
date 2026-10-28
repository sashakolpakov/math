import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorModulePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorRightNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence

/-! # Tensor Pullback Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorPullbackFunctor

noncomputable section

/-! The proved tensor pullback isomorphism is natural in the arbitrary module factor. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u
local instance e33TensorPullbackFunctorModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := Module.SheafMonoidal.moduleMonoidalCategory X
variable {X Y : Scheme.{u}}

def lineBundleTensorPullbackFunctorIso (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y) :
    (TensorEquivalence.lineBundleTensorEquivalence L).functor ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙ (TensorEquivalence.lineBundleTensorEquivalence (L.pullback f)).functor :=
  NatIso.ofComponents (fun M =>
    (Scheme.Modules.pullback f).mapIso (Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf M) ≪≫
      TensorModulePullback.lineBundleTensorModulePullbackIso f L M ≪≫
      (Module.MonoidalTensorComparison.moduleMonoidalTensorIso (L.pullback f).sheaf ((Scheme.Modules.pullback f).obj M)).symm) (by
    intro M M' h
    let P := Scheme.Modules.pullback f
    change P.map (L.sheaf ◁ h) ≫
        (P.map (Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf M').hom ≫
          Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M' ≫
          (Module.MonoidalTensorComparison.moduleMonoidalTensorIso (P.obj L.sheaf) (P.obj M')).inv) =
      (P.map (Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf M).hom ≫
        Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M ≫
        (Module.MonoidalTensorComparison.moduleMonoidalTensorIso (P.obj L.sheaf) (P.obj M)).inv) ≫
          ((P.obj L.sheaf) ◁ P.map h)
    apply (cancel_mono (Module.MonoidalTensorComparison.moduleMonoidalTensorIso (P.obj L.sheaf) (P.obj M')).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Module.MonoidalTensorRightNaturality.moduleMonoidalTensorIso_natural_right]
    simp only [Iso.inv_hom_id_assoc]
    calc
      P.map (L.sheaf ◁ h) ≫ P.map (Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf M').hom ≫
          Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M' =
        P.map ((L.sheaf ◁ h) ≫ (Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf M').hom) ≫
          Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M' := by rw [P.map_comp, Category.assoc]
      _ = P.map ((Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf M).hom ≫ Tensor.Bifunctor.tensorModuleMap (𝟙 L.sheaf) h) ≫
          Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M' :=
        congrArg (fun k => P.map k ≫ Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M')
          (Module.MonoidalTensorRightNaturality.moduleMonoidalTensorIso_natural_right L.sheaf h)
      _ = P.map (Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf M).hom ≫
          Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M ≫
          Tensor.Bifunctor.tensorModuleMap (𝟙 (P.obj L.sheaf)) (P.map h) := by
        rw [P.map_comp, Category.assoc, Tensor.PullbackComparison.tensorPullbackComparison_natural, P.map_id])

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorPullbackFunctor
