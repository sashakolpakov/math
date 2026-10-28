import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.UnitTensorEquivalence

/-! # Coordinates From Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor coordinates in a local rank-one frame are products of the ordinary frame coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M)

def CompatibleSheaf.CompatibleSheafFrames.tensorCoordinate (d : ℕ) (V : X.Opens) (i : ι) (hi : V ≤ U i) :
    TensorPower.Presheaf.tensorPowerSections M d V ≃ₗ[Γ(X, V)] Γ(X, V) :=
  (PiTensorProduct.congr (fun _ : Fin d => (E.frame V i hi).symm)).trans (Finite.UnitTensorEquivalence.finiteUnitTensorEquiv Γ(X, V) (Fin d))

theorem CompatibleSheaf.CompatibleSheafFrames.tensorCoordinate_tprod (d : ℕ) (V : X.Opens) (i : ι) (hi : V ≤ U i) (x : Fin d → Γ(M, V)) :
    E.tensorCoordinate d V i hi (PiTensorProduct.tprod Γ(X, V) x) = ∏ k, (E.frame V i hi).symm (x k) := by
  exact (congrArg (Finite.UnitTensorEquivalence.finiteUnitTensorEquiv Γ(X, V) (Fin d))
    (PiTensorProduct.congr_tprod (fun _ : Fin d => (E.frame V i hi).symm) x)).trans
      (Finite.UnitTensorEquivalence.finiteUnitTensorEquiv_tprod Γ(X, V) (Fin d) _)

theorem CompatibleSheaf.CompatibleSheafFrames.tensorCoordinate_tprod_change (d : ℕ) (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j)
    (x : Fin d → Γ(M, V)) :
    E.tensorCoordinate d V i hi (PiTensorProduct.tprod Γ(X, V) x) =
      (D.value V i j hi hj).val ^ d * E.tensorCoordinate d V j hj (PiTensorProduct.tprod Γ(X, V) x) := by
  rw [E.tensorCoordinate_tprod, E.tensorCoordinate_tprod]
  simp_rw [E.coordinate_change V i j hi hj]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
