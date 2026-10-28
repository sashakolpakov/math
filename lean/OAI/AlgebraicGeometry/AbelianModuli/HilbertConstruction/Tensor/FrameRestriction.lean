import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.FrameComparisons

/-! # Frame Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The local tensor-frame comparisons commute with restriction on every tensor, by linear generation from pure tensors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (d : ℕ) (F : CompatibleSheaf.CompatibleSheafFrames (D.power d) N)

theorem CompatibleSheaf.CompatibleSheafFrames.tensorComparison_restrict (V W : X.Opens) (h : W ≤ V) (i j : ι)
    (hi : W ≤ U i) (hj : V ≤ U j) (z : TensorPower.Presheaf.tensorPowerSections M d V) :
    E.tensorComparison d F W i hi (TensorPower.Presheaf.tensorPowerRestriction M d (homOfLE h).op z) =
      N.presheaf.map (homOfLE h).op (E.tensorComparison d F V j hj z) := by
  refine PiTensorProduct.induction_on (R := Γ(X, V)) (s := fun _ : Fin d => Γ(M, V)) z ?_ ?_
  · intro r x
    let t := PiTensorProduct.tprod Γ(X, V) x
    have hl := (TensorPower.Presheaf.tensorPowerPresheaf M d).map_smul (homOfLE h).op r t
    have hr := (congrArg (N.presheaf.map (homOfLE h).op)
      ((E.tensorComparison d F V j hj).map_smul r t)).trans
        (Scheme.Modules.map_smul N (homOfLE h) r (E.tensorComparison d F V j hj t))
    exact ((congrArg (E.tensorComparison d F W i hi) hl).trans
      ((E.tensorComparison d F W i hi).map_smul _ _)).trans
        ((congrArg (fun a : Γ(N, W) => (X.presheaf.map (homOfLE h).op r) • a)
          (E.tensorComparison_restrict_tprod d F V W h i j hi hj x)).trans hr.symm)
  · intro x y hx hy
    have hl := (congrArg (E.tensorComparison d F W i hi)
      ((TensorPower.Presheaf.tensorPowerRestriction M d (homOfLE h).op).hom.map_add x y)).trans
        ((E.tensorComparison d F W i hi).map_add _ _)
    have hr := (congrArg (N.presheaf.map (homOfLE h).op)
      ((E.tensorComparison d F V j hj).map_add x y)).trans
        ((N.presheaf.map (homOfLE h).op).hom.map_add _ _)
    exact hl.trans ((congrArg₂ (fun a b : Γ(N, W) => a + b) hx hy).trans hr.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
