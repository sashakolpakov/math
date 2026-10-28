import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange

/-! # Refinement Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient

noncomputable section

/-! Finite nonempty Cech refinement commutes with the actual additive
coefficient-change isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z w' z' t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{t} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{t} B]
  (G : A ⥤ B) [G.Additive]
  {ι κ : Type t} [Finite ι] [Finite κ] (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (P : Cᵒᵖ ⥤ A)

theorem finite_indices (n : SimplexCategory) : Finite ((IntegralComparison.NonemptyCechNerve.nerve U).obj (op n)).I :=
  inferInstanceAs (Finite (Fin (n.len + 1) → ι))

theorem natural : (G.mapHomologicalComplex (.up ℕ)).map (Refinement.NonemptyCechRefinement.map U V r P) ≫
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve V) (finite_indices V) P).hom =
      (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve U) (finite_indices U) P).hom ≫
        Refinement.NonemptyCechRefinement.map U V r (P ⋙ G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change G.map ((Refinement.NonemptyCechRefinement.map U V r P).f n) ≫
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve V) (finite_indices V) P).hom.f n =
      (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve U) (finite_indices U) P).hom.f n ≫
        (Refinement.NonemptyCechRefinement.map U V r (P ⋙ G)).f n
  rw [GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f, GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  let En := (IntegralComparison.NonemptyCechNerve.nerve U).obj (op ⦋n⦌)
  let Em := (IntegralComparison.NonemptyCechNerve.nerve V).obj (op ⦋n⦌)
  let a := (Refinement.NonemptyCechRefinement.nerveMap U V r).app (op ⦋n⦌)
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.piComparison_natural G
    (fun i : En.I => P.obj (op (En.obj i))) (fun i : Em.I => P.obj (op (Em.obj i))) a.f
    (fun i => P.map (a.φ i).op)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient
