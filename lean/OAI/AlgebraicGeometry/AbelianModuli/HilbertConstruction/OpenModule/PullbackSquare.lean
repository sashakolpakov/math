import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.BaseChangeMate

/-! # Pullback Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.PullbackSquare.OpenPullbackSquare

noncomputable section

/-! The isomorphism of composed inverse images and its canonical mate. -/
open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The left-adjoint square obtained from the isomorphism of composed
direct images. -/
def adjointPullbackSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm
    (BaseChangeMate.OpenPullbackSquare.pushforwardSquareIso f U)

/-- The canonical restriction map is the mate of the invertible pullback square. -/
theorem rightMate :
    (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
      (TwoSquare.mk _ _ _ _ (adjointPullbackSquare f U).hom)).natTrans =
        BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U := by
  let γ := TwoSquare.mk _ _ _ _ (BaseChangeMate.OpenPullbackSquare.pushforwardSquareIso f U).hom
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι) γ
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))).symm.injective
  rw [Equiv.symm_apply_apply]
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.PullbackSquare.OpenPullbackSquare
