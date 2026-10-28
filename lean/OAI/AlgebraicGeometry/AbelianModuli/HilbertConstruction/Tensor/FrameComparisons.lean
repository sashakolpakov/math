import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.CoordinatesFromFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedOpenFrameTransitions

/-! # Frame Comparisons -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Local tensor-product coordinates give frame-independent comparisons with any sheaf realizing the powered cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (d : ℕ) (F : CompatibleSheaf.CompatibleSheafFrames (D.power d) N)

def CompatibleSheaf.CompatibleSheafFrames.tensorComparison (V : X.Opens) (i : ι) (hi : V ≤ U i) :
    TensorPower.Presheaf.tensorPowerSections M d V ≃ₗ[Γ(X, V)] Γ(N, V) :=
  (E.tensorCoordinate d V i hi).trans (F.frame V i hi)

theorem CompatibleSheaf.CompatibleSheafFrames.tensorComparison_independent (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    E.tensorComparison d F V i hi = E.tensorComparison d F V j hj := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  exact (congrArg (F.frame V i hi) (E.tensorCoordinate_tprod_change d V i j hi hj x)).trans
    (F.change V i j hi hj (E.tensorCoordinate d V j hj (PiTensorProduct.tprod Γ(X, V) x)))

theorem CompatibleSheaf.CompatibleSheafFrames.tensorCoordinate_restrict_tprod (V W : X.Opens) (h : W ≤ V) (i : ι) (hi : V ≤ U i)
    (x : Fin d → Γ(M, V)) :
    E.tensorCoordinate d W i (h.trans hi)
      (TensorPower.Presheaf.tensorPowerRestriction M d (homOfLE h).op (PiTensorProduct.tprod Γ(X, V) x)) =
    X.presheaf.map (homOfLE h).op (E.tensorCoordinate d V i hi (PiTensorProduct.tprod Γ(X, V) x)) := by
  rw [TensorPower.Presheaf.tensorPowerRestriction_tprod, E.tensorCoordinate_tprod, E.tensorCoordinate_tprod]
  exact (Finset.prod_congr rfl (fun k _ => E.coordinate_restrict V W h i hi (x k))).trans
    (map_prod (X.presheaf.map (homOfLE h).op).hom (fun k => (E.frame V i hi).symm (x k)) Finset.univ).symm

theorem CompatibleSheaf.CompatibleSheafFrames.tensorComparison_restrict_tprod (V W : X.Opens) (h : W ≤ V) (i j : ι)
    (hi : W ≤ U i) (hj : V ≤ U j) (x : Fin d → Γ(M, V)) :
    E.tensorComparison d F W i hi
      (TensorPower.Presheaf.tensorPowerRestriction M d (homOfLE h).op (PiTensorProduct.tprod Γ(X, V) x)) =
    N.presheaf.map (homOfLE h).op (E.tensorComparison d F V j hj (PiTensorProduct.tprod Γ(X, V) x)) := by
  have he := congrArg (fun e : TensorPower.Presheaf.tensorPowerSections M d W ≃ₗ[Γ(X, W)] Γ(N, W) =>
      e (TensorPower.Presheaf.tensorPowerRestriction M d (homOfLE h).op (PiTensorProduct.tprod Γ(X, V) x)))
    (E.tensorComparison_independent d F W i j hi (h.trans hj))
  exact he.trans ((congrArg (F.frame W j (h.trans hj)) (E.tensorCoordinate_restrict_tprod d V W h j hj x)).trans
    (F.restrict V W h j hj (E.tensorCoordinate d V j hj (PiTensorProduct.tprod Γ(X, V) x))).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
