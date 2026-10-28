import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.ProductComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.OfPowersComposition

/-! # Tensor Power Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerComparison

noncomputable section

/-! Local tensor-power comparisons between pullbacks of the two global module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {L M : Y.Modules}

def localTensorPowerComparisonIso
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    [IsIso e] [IsIso t] (n : ℕ) :
    (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n) ≅
      (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L n) (TensorPower.PowerSheaf.tensorPowerModule M n)) :=
  TensorPower.ProductPullbacks.tensorPowerOfTensorPullbackIso f L M n ≪≫ TensorPower.FrameComparison.tensorPowerFrameComparisonIso e t n ≪≫
    (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso f L M n).symm

theorem localTensorPowerComparisonIso_spec
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    [IsIso e] [IsIso t] (n : ℕ) :
    (localTensorPowerComparisonIso f e t n).hom ≫ (TensorPower.ProductPullbacks.tensorOfPowersPullbackIso f L M n).hom =
      (TensorPower.ProductPullbacks.tensorPowerOfTensorPullbackIso f L M n).hom ≫ (TensorPower.FrameComparison.tensorPowerFrameComparisonIso e t n).hom := by
  simp only [localTensorPowerComparisonIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem localTensorPowerComparisonIso_independent
    (e e' : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L)
    (t t' : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    [IsIso e] [IsIso e'] [IsIso t] [IsIso t'] (n : ℕ) :
    localTensorPowerComparisonIso f e t n = localTensorPowerComparisonIso f e' t' n := by
  unfold localTensorPowerComparisonIso
  rw [TensorPower.FrameComparison.tensorPowerFrameComparisonIso_independent e e' t t' n]

def localTensorPowerRestrictionIso
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    [IsIso e] [IsIso t] (n : ℕ) :
    (TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n).restrict f ≅
      (Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L n) (TensorPower.PowerSheaf.tensorPowerModule M n)).restrict f :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app _ ≪≫ localTensorPowerComparisonIso f e t n ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback f).app _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerComparison
