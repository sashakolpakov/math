import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.ProductAxes
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatJointInjection

/-! # Product Axes -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProductAxes.Construction

noncomputable section

/-! Axis detection after the actual extension to algebraic ℓ-adic coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A B : Scheme.{u}}
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p] [GeometricallyIntegral p]
  (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [GeometricallyIntegral q]
  (ℓ : ℕ) [Fact ℓ.Prime]
  (e : Spec (CommRingCat.of K) ⟶ A) (he : e ≫ p = 𝟙 _)
  (b : Spec (CommRingCat.of K) ⟶ B) (hb : b ≫ q = 𝟙 _)

/-- Flat extension of the proved integral joint restriction map. -/
theorem algebraicEllAdicH1_axes_injective : Function.Injective
    ((CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ
        (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left).prod
      (CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (Proper.AffineBaseChange.Construction.properProductSection p q e he))) := by
  have : FaithfulSMul (ℤ_[ℓ]) (AlgebraicClosure ℚ_[ℓ]) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [IsScalarTower.algebraMap_eq (ℤ_[ℓ]) (ℚ_[ℓ]) (AlgebraicClosure ℚ_[ℓ])]
      exact (RingHom.injective (algebraMap (ℚ_[ℓ]) (AlgebraicClosure ℚ_[ℓ]))).comp
        (show Function.Injective (algebraMap (ℤ_[ℓ]) (ℚ_[ℓ])) from Subtype.val_injective))
  exact FlatJointInjection.Construction.baseChange_prod_injective (AlgebraicClosure ℚ_[ℓ]) _ _
    (Product.ProductAxes.Construction.integralEllAdicH1_axes_injective p q ℓ e he b hb)

/-- Both axis restrictions detect zero in the actual algebraic-coefficient H¹. -/
theorem algebraicEllAdicH1_eq_zero_of_axes
    (x : Cohomology.Construction.EllAdicH1AlgebraicCoefficients ℓ (pullback p q))
    (hfirst : CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ
      (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left x = 0)
    (hsecond : CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (Proper.AffineBaseChange.Construction.properProductSection p q e he) x = 0) :
    x = 0 := by
  apply algebraicEllAdicH1_axes_injective p q ℓ e he b hb
  apply Prod.ext
  · exact hfirst.trans (map_zero _).symm
  · exact hsecond.trans (map_zero _).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProductAxes.Construction
