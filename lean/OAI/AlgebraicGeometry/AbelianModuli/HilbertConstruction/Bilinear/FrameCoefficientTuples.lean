import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InverseFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalTuples

/-! # Frame Coefficient Tuples -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameCoefficientTuples

noncomputable section

/-! A bilinear pairing with reciprocal local frames gives a linear tuple of prospective section coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M Q : X.Modules} (F : CompatibleSheaf.CompatibleSheafFrames D.reciprocal Q)
variable (β : Sheaves.SheafBilinearMap M Q (Line.Bundles.structureModule X))

def pairingFrameCoefficient (s : Γ(M, ⊤)) (i : ι) : Γ(X, U i) :=
  β.app (U i) (M.presheaf.map (U i).leTop.op s) (F.frame (U i) i le_rfl 1)

def pairingFrameTupleMap : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] OpenFrame.GlobalTuples.OpenFrameGlobalTuple U where
  toFun s i := pairingFrameCoefficient F β s i
  map_add' s t := by
    ext i
    change β.app (U i) (M.presheaf.map (U i).leTop.op (s + t)) (F.frame (U i) i le_rfl 1) = _
    rw [map_add, map_add, LinearMap.add_apply]
    rfl
  map_smul' r s := by
    ext i
    change β.app (U i) (M.presheaf.map (U i).leTop.op (r • s)) (F.frame (U i) i le_rfl 1) =
      X.presheaf.map (U i).leTop.op r * pairingFrameCoefficient F β s i
    rw [M.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
    rfl

theorem pairingFrameCoefficient_restrict (s : Γ(M, ⊤)) (V : X.Opens) (i : ι) (hi : V ≤ U i) :
    X.presheaf.map (homOfLE hi).op (pairingFrameCoefficient F β s i) =
      β.app V (M.presheaf.map V.leTop.op s) (F.frame V i hi 1) := by
  have h := β.naturality (homOfLE hi) (M.presheaf.map (U i).leTop.op s)
    (F.frame (U i) i le_rfl 1)
  have hf := (F.restrict (U i) V hi i le_rfl 1).trans
    (congrArg (F.frame V i hi) ((X.presheaf.map (homOfLE hi).op).hom.map_one))
  have hs : M.presheaf.map (homOfLE hi).op (M.presheaf.map (U i).leTop.op s) =
      M.presheaf.map V.leTop.op s := by
    rw [← M.presheaf.map_comp_apply]
    rfl
  exact h.trans (congrArg₂ (fun (a : Γ(M, V)) (b : Γ(Q, V)) => β.app V a b) hs hf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameCoefficientTuples
