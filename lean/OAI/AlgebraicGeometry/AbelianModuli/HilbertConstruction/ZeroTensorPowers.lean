import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers

/-! # Zero Tensor Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The zeroth tensor power is the structure module, independently of its input sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def Tensor.Powers.SheafMultilinearMap.emptySource {L P : X.Modules} (β : Tensor.Powers.SheafMultilinearMap L 0 P)
    (M : X.Modules) : Tensor.Powers.SheafMultilinearMap M 0 P where
  app U := MultilinearMap.constOfIsEmpty Γ(X, U) (fun _ : Fin 0 => Γ(M, U)) (β.app U Fin.elim0)
  naturality {_ V} h _ :=
    (β.naturality h Fin.elim0).trans (congrArg (β.app V) (Subsingleton.elim _ _))

def Tensor.Powers.SheafMultilinearMap.emptySourceEquiv (L M P : X.Modules) :
    Tensor.Powers.SheafMultilinearMap L 0 P ≃ Tensor.Powers.SheafMultilinearMap M 0 P where
  toFun β := β.emptySource M
  invFun β := β.emptySource L
  left_inv β := by
    ext U s
    exact congrArg (β.app U) (Subsingleton.elim _ _)
  right_inv β := by
    ext U s
    exact congrArg (β.app U) (Subsingleton.elim _ _)

theorem ZeroTensorPowers.isTensorPower_zero (L : X.Modules) : Tensor.Powers.IsTensorPower L 0 (Line.Bundles.structureModule X) := by
  obtain ⟨β, hβ⟩ := LineBundle.Powers.structureModule_isTensorPower X 0
  refine ⟨β.emptySource L, fun P => ?_⟩
  have he : (fun f : Line.Bundles.structureModule X ⟶ P => (β.emptySource L).postcomp f) =
      fun f => Tensor.Powers.SheafMultilinearMap.emptySourceEquiv (Line.Bundles.structureModule X) L P (β.postcomp f) := by
    funext f
    ext U s
    rfl
  rw [he]
  exact (Tensor.Powers.SheafMultilinearMap.emptySourceEquiv (Line.Bundles.structureModule X) L P).bijective.comp (hβ P)

def Line.Bundles.LineBundle.tensorPowerZeroIso (L : Line.Bundles.LineBundle X) :
    (L.tensorPower 0).sheaf ≅ Line.Bundles.structureModule X :=
  ((L.tensorPower_isTensorPower 0).unique (ZeroTensorPowers.isTensorPower_zero L.sheaf)).some

def Line.Bundles.LineBundle.tensorPowerOneIso (L : Line.Bundles.LineBundle X) :
    (L.tensorPower 1).sheaf ≅ L.sheaf :=
  ((L.tensorPower_isTensorPower 1).unique (Tensor.Powers.isTensorPower_one L.sheaf)).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
