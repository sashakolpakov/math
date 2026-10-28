import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Rigidity
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf

/-! # Group Rigidity -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity

noncomputable section

/-! Pointed morphisms between the abelian varieties used in Homomorphisms respect
their group laws. The input is geometric rigidity, with no group-law
compatibility imposed on the morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem integral_smooth_proper_connected_group
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] : IsIntegral A.left := by
  have : IrreducibleSpace A.left := Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_of_connected_group A
  have : IsReduced A.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field A.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced A.left

theorem integral_square_smooth_proper_connected_group
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] :
    IsIntegral (A ⊗ A).left := by
  have : Smooth (A ⊗ A).hom := by dsimp; infer_instance
  have : IsProper (A ⊗ A).hom := by dsimp; infer_instance
  have : GeometricallyConnected (A ⊗ A).hom :=
    GeometricallyConnected.comp (pullback.fst A.hom A.hom) A.hom
  exact integral_smooth_proper_connected_group (A ⊗ A)

theorem pointed_isMonHom
    {k : Type u} [Field k] [IsAlgClosed k]
    (A B : Over (Spec (.of k))) [groupA : GrpObj A] [commA : IsCommMonObj A] [groupB : GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  have : IsIntegral (A ⊗ A).left := integral_square_smooth_proper_connected_group A
  let l : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let r : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  have hlμ : l ≫ μ[A] = 𝟙 A := by
    change (1 : A ⟶ A) * 𝟙 A = 𝟙 A
    exact one_mul _
  have hrμ : r ≫ μ[A] = 𝟙 A := by
    change 𝟙 A * (1 : A ⟶ A) = 𝟙 A
    exact mul_one _
  have h1 : (1 : A ⟶ A) ≫ f = 1 := by
    rw [Hom.one_def, Category.assoc, hf]
    rfl
  let d : A ⊗ A ⟶ B := (μ[A] ≫ f) / ((fst A A ≫ f) * (snd A A ≫ f))
  have hld : l ≫ d = 1 := by
    simp only [d, GrpObj.comp_div, MonObj.comp_mul]
    rw [← Category.assoc, hlμ, Category.id_comp]
    simp [l, h1, ← Category.assoc, ← Hom.one_def]
  have hrd : r ≫ d = 1 := by
    simp only [d, GrpObj.comp_div, MonObj.comp_mul]
    rw [← Category.assoc, hrμ, Category.id_comp]
    simp [r, h1, ← Category.assoc, ← Hom.one_def]
  have hd : d = 1 := by
    have h := ArithmeticGeometry.OrdinaryLocus.Openness.Rigidity.Construction.rigidity_of_constant_fiber A A B η[A] η[A] η[B] d hld
    change d = fst A A ≫ r ≫ d at h
    simpa only [hrd, MonObj.comp_one] using h
  refine ⟨hf, ?_⟩
  have hm := div_eq_one.mp hd
  change μ[A] ≫ f = (fst A A ≫ f) * (snd A A ≫ f) at hm
  rw [hm, Hom.mul_def]
  congr 1

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity
