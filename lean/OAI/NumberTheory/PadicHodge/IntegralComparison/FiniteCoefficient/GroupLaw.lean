import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Functoriality
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Exponent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.ProductAxes
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.Axes

/-! # Group Law -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.GroupLaw

noncomputable section

/-! The group law acts additively on the actual finite-coefficient H¹
of a smooth proper geometrically integral group scheme. This is the
finite-level input to detection by multiplication covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Functoriality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]

omit [Fact (Nat.Prime ℓ)] in
theorem pullback_through_point {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Spec (.of k) ⟶ Y)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y).H 1) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (f ≫ g) 1 x = 0 := by
  rw [← Functoriality.finiteEllAdicPullback_comp]
  rw [AlgebraicGeometry.FormalGeometry.Completion.Geometric.PointCohomology.Construction.geometricPoint_sheaf_cohomology_eq_zero k
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n (Spec (.of k))) 0
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n g 1 x), map_zero]

variable (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

omit [IsAlgClosed k] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem first_axis :
    (AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductAxis.Construction.properProductFirstAxisOver A A (η[A]).left (η[A]).w).left =
      (AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction.groupFirstAxis k A).left := by
  apply pullback.hom_ext <;> simp [AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductAxis.Construction.properProductFirstAxisOver, AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction.groupFirstAxis]

omit [IsAlgClosed k] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem second_axis :
    AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineBaseChange.Construction.properProductSection A.hom A.hom (η[A]).left (η[A]).w =
      (AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction.groupSecondAxis k A).left := by
  apply pullback.hom_ext <;> simp [AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineBaseChange.Construction.properProductSection, AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction.groupSecondAxis]

theorem axes_detect
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n (A ⊗ A).left).H 1)
    (hfirst : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction.groupFirstAxis k A).left 1 x = 0)
    (hsecond : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction.groupSecondAxis k A).left 1 x = 0) : x = 0 := by
  apply AlgebraicGeometry.FormalGeometry.Completion.Product.ProductAxes.Construction.finiteEllAdicH1_eq_zero_of_axes A.hom A.hom ℓ
    (η[A]).left (η[A]).w (η[A]).left (η[A]).w n x
  · rw [first_axis]
    exact hfirst
  · rw [second_axis]
    exact hsecond

theorem group_law (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (μ[A]).left 1 x =
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (fst A A).left 1 x +
        AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (snd A A).left 1 x := by
  have hz : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (toUnit A ≫ η[A]).left 1 x = 0 :=
    pullback_through_point ℓ n A.hom (η[A]).left x
  apply sub_eq_zero.mp
  apply axes_detect ℓ n A
  · simp only [map_sub, map_add, Functoriality.finiteEllAdicPullback_comp, ← Over.comp_left]
    simp only [AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction.groupFirstAxis, lift_comp_one_right, lift_fst, lift_snd,
      Over.id_left, Functoriality.finiteEllAdicPullback_id, hz, add_zero, sub_self]
  · simp only [map_sub, map_add, Functoriality.finiteEllAdicPullback_comp, ← Over.comp_left]
    simp only [AlgebraicGeometry.FormalGeometry.Completion.Product.Axes.Construction.groupSecondAxis, lift_comp_one_left, lift_fst, lift_snd,
      Over.id_left, Functoriality.finiteEllAdicPullback_id, hz, zero_add, sub_self]

theorem pullback_mul {T : Over (Spec (.of k))} (f g : T ⟶ A)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (f * g).left 1 x =
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f.left 1 x + AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n g.left 1 x := by
  change AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (lift f g ≫ μ[A]).left 1 x = _
  rw [Over.comp_left, ← Functoriality.finiteEllAdicPullback_comp, group_law, map_add,
    Functoriality.finiteEllAdicPullback_comp, Functoriality.finiteEllAdicPullback_comp,
    ← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd]

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
omit [Fact (Nat.Prime ℓ)] in
theorem pullback_one {T : Over (Spec (.of k))}
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (1 : T ⟶ A).left 1 x = 0 :=
  pullback_through_point ℓ n T.hom (η[A]).left x

theorem pullback_pow {T : Over (Spec (.of k))} (f : T ⟶ A) (m : ℕ)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (f ^ m).left 1 x =
      m • AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f.left 1 x := by
  induction m with
  | zero => rw [pow_zero, pullback_one, zero_smul]
  | succ m ih => rw [pow_succ, pullback_mul, ih, add_nsmul, one_nsmul]

theorem multiplication_pullback (m : ℕ)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n ((𝟙 A : A ⟶ A) ^ m).left 1 x = m • x := by
  rw [pullback_pow, Over.id_left, Functoriality.finiteEllAdicPullback_id]

theorem multiplication_pow_pullback_zero
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n ((𝟙 A : A ⟶ A) ^ (ℓ ^ n)).left 1 x = 0 := by
  rw [multiplication_pullback]
  exact Exponent.cohomology_nsmul ℓ n A.left 1 x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.GroupLaw
