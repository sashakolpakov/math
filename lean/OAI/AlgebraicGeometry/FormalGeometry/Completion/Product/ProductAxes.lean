import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorAxesLift
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection

/-! # Product Axes -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.ProductAxes.Construction

noncomputable section

/-! Restrictions to the two actual product axes detect degree-one cohomology classes. -/

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

/-- Actual finite-coefficient H¹ is detected by the two axes. -/
theorem finiteEllAdicH1_eq_zero_of_axes (n : ℕ)
    (x : (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n (pullback p q)).H 1)
    (hfirst : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n
      (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left 1 x = 0)
    (hsecond : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 x = 0) :
    x = 0 := by
  obtain ⟨E, rfl⟩ := FiniteTorsor.App.Construction.finiteCoefficientExtension_exists ℓ n (pullback p q) x
  exact TorsorAxesLift.Construction.productTorsor_class_eq_zero_of_axes p q E e he b hb hfirst hsecond

/-- Actual integral H¹ is detected by the two axes, through all finite reductions. -/
theorem integralEllAdicH1_eq_zero_of_axes
    (x : (pullback p q : Scheme.{u}).EllAdicCohomology ℓ 1)
    (hfirst : ProetalePullback.Construction.integralEllAdicPullback ℓ
      (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left 1 x = 0)
    (hsecond : ProetalePullback.Construction.integralEllAdicPullback ℓ (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 x = 0) :
    x = 0 := by
  apply Finite.CoefficientDetection.Construction.integralEllAdicH1_eq_zero_of_finiteReduction ℓ (pullback p q)
  intro n
  apply finiteEllAdicH1_eq_zero_of_axes p q ℓ e he b hb n
  · exact (Finite.CoefficientPullback.Construction.integralEllAdicFiniteReduction_pullback ℓ n
      (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left 1 x).trans
        (by rw [hfirst, map_zero])
  · exact (Finite.CoefficientPullback.Construction.integralEllAdicFiniteReduction_pullback ℓ n
      (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1 x).trans (by rw [hsecond, map_zero])

/-- The joint integral restriction map is injective. -/
theorem integralEllAdicH1_axes_injective : Function.Injective
    ((CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ
        (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left 1).prod
      (CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ (Proper.AffineBaseChange.Construction.properProductSection p q e he) 1)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  exact integralEllAdicH1_eq_zero_of_axes p q ℓ e he b hb x
    (congrArg Prod.fst hx) (congrArg Prod.snd hx)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.ProductAxes.Construction
