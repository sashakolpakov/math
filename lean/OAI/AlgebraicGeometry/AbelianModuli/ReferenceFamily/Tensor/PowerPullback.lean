import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerSheafSplitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.TensorRestriction

/-! # Power Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerPullback

noncomputable section

/-! Positive tensor powers commute with arbitrary scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}}

def tensorPowerOneIso (L : Y.Modules) : HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L 1 ≅ L :=
  Classical.choice ((HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule_isTensorPower L 1).unique (HilbertConstruction.Tensor.Powers.isTensorPower_one L))

def tensorPowerPositivePullbackIso (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L (n + 1)) ≅
      HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) (n + 1) := by
  induction n with
  | zero =>
    exact (Scheme.Modules.pullback f).mapIso (tensorPowerOneIso L) ≪≫
      (tensorPowerOneIso ((Scheme.Modules.pullback f).obj L)).symm
  | succ n ih =>
    exact (Scheme.Modules.pullback f).mapIso (PowerSheafSplitting.tensorPowerSuccSheafIso L (n + 1)) ≪≫
      Classical.choice (SheafCohomology.Projective.PullbackTensorObj.Scheme.Modules.nonempty_pullback_tensorObj f
        (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L (n + 1)) L) ≪≫
      HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ih (Iso.refl _) ≪≫
      (PowerSheafSplitting.tensorPowerSuccSheafIso ((Scheme.Modules.pullback f).obj L) (n + 1)).symm

theorem isTensorPower_pullback_positive (f : X ⟶ Y) {L P : Y.Modules} {n : ℕ}
    (hn : 0 < n) (hP : HilbertConstruction.Tensor.Powers.IsTensorPower L n P) :
    HilbertConstruction.Tensor.Powers.IsTensorPower ((Scheme.Modules.pullback f).obj L) n
      ((Scheme.Modules.pullback f).obj P) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let e := Classical.choice (hP.unique (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule_isTensorPower L (m + 1)))
  exact (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule_isTensorPower ((Scheme.Modules.pullback f).obj L) (m + 1)).of_targetIso
    (((Scheme.Modules.pullback f).mapIso e ≪≫ tensorPowerPositivePullbackIso f L m).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerPullback
