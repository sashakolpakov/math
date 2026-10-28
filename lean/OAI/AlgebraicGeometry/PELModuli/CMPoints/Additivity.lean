import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.Multiplication
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RealizedIsogenies

/-! # Additivity -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Additivity

noncomputable section

/-! Addition of actual algebraic maps is addition on rational H1.
This uses the checked primitive-class formula for abelian multiplication. -/

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

theorem abelianH1Pullback_mul {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f g : A.toOver ⟶ B.toOver) :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (f * g) = ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f + ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g := by
  let p : AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A ⟶ AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop B := TopCat.ofHom
    ⟨fun x => (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x),
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).prodMk (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map g)⟩
  have hm : p ≫ AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop B = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (f * g) := by
    apply TopCat.ext
    intro x
    exact (MonObj.comp_mul x f g).symm
  have hf : p ≫ TopCat.prodFst = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f := rfl
  have hg : p ≫ TopCat.prodSnd = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g := rfl
  ext c
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (f * g)) 1 c =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) 1 c +
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g) 1 c
  have h := congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) p 1)
    (AbelianModuli.ReferenceFamily.Product.Multiplication.abelianH1_multiplication B c)
  simpa only [map_add, AbelianModuli.ReferenceFamily.Product.Multiplication.productH1Left, AbelianModuli.ReferenceFamily.Product.Multiplication.productH1Right,
    AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.pullback_comp_apply, hm, hf, hg] using h

theorem abelianH1Pullback_one (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (1 : A.toOver ⟶ B.toOver) = 0 := by
  have h := abelianH1Pullback_mul (1 : A.toOver ⟶ B.toOver) 1
  rw [one_mul] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

theorem abelianH1Pullback_prod {I : Type*} {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (s : Finset I) (f : I → (A.toOver ⟶ B.toOver)) :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (∏ i ∈ s, f i) = ∑ i ∈ s, ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, abelianH1Pullback_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, abelianH1Pullback_mul, ih]

theorem algebraic_mul_isMonHom {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f g : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  exact inferInstanceAs (IsMonHom (CartesianMonoidalCategory.lift f g ≫ μ[B.toOver]))

theorem algebraic_one_isMonHom (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IsMonHom (1 : A.toOver ⟶ B.toOver) :=
  inferInstanceAs (IsMonHom (CartesianMonoidalCategory.toUnit A.toOver ≫ η[B.toOver]))

theorem algebraic_prod_isMonHom {I : Type*} {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (s : Finset I) (f : I → (A.toOver ⟶ B.toOver)) (hf : ∀ i ∈ s, IsMonHom (f i)) :
    IsMonHom (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using algebraic_one_isMonHom A B
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    let : IsMonHom (f i) := hf i (Finset.mem_insert_self i s)
    let : IsMonHom (∏ j ∈ s, f j) := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact algebraic_mul_isMonHom _ _

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Additivity
