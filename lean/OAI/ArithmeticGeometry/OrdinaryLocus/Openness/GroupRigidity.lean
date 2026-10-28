import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Rigidity
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral

/-! # Group Rigidity -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupRigidity.Construction

noncomputable section

/-! Rigidity consequences for the smooth proper groups in Openness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem isIntegral_product_connected_smooth_proper_groups
    {k : Type u} [Field k] [IsAlgClosed k]
    (A B : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom] :
    IsIntegral (A ⊗ B).left := by
  have : Smooth (A ⊗ B).hom := by dsimp; infer_instance
  have : IsProper (A ⊗ B).hom := by dsimp; infer_instance
  have : GeometricallyConnected (A ⊗ B).hom :=
    GeometricallyConnected.comp (pullback.fst A.hom B.hom) A.hom
  exact ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group (A ⊗ B)

/-- A pointed morphism from a proper group with integral square is a group homomorphism. -/
theorem isMonHom_of_preserves_unit_of_integral_square
    {k : Type u} [Field k] [IsAlgClosed k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
    [IsProper A.hom] [IsIntegral (A ⊗ A).left]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
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
    have h := Rigidity.Construction.rigidity_of_constant_fiber A A B η[A] η[A] η[B] d hld
    change d = fst A A ≫ r ≫ d at h
    simpa only [hrd, MonObj.comp_one] using h
  refine ⟨hf, ?_⟩
  have hm := div_eq_one.mp hd
  change μ[A] ≫ f = (fst A A ≫ f) * (snd A A ≫ f) at hm
  rw [hm, Hom.mul_def]
  congr 1

/-- Every unit-preserving scheme morphism from an Openness abelian variety
to an algebraic group respects multiplication. -/
theorem isMonHom_of_preserves_unit
    {k : Type u} [Field k] [IsAlgClosed k]
    (A B : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  have : IsIntegral (A ⊗ A).left := isIntegral_product_connected_smooth_proper_groups A A
  exact isMonHom_of_preserves_unit_of_integral_square A B f hf

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupRigidity.Construction
