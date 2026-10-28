import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient

/-! # Product Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductCoefficient.NonemptyCechProductCoefficient

noncomputable section

/-! Tuple-product reindexing commutes with the original finite Cech
coefficient-change isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe t u v uD vD w z w' z'
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{t} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{t} B]
  (F : C ⥤ D) (G : A ⥤ B) [G.Additive]
  {ι : Type t} [Finite ι] (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (P : Dᵒᵖ ⥤ A)

omit [Finite ι] in
theorem hom_f (n : ℕ) : (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).hom.f n =
    (ProductBaseChange.NonemptyCechProductBaseChange.componentIso F U P ⦋n⦌).hom := rfl

theorem natural : (G.mapHomologicalComplex (.up ℕ)).map (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).hom ≫
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve (F.obj ∘ U))
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (F.obj ∘ U)) P).hom =
      (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve U)
        (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (F.op ⋙ P)).hom ≫
          (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U (P ⋙ G)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change G.map ((ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).hom.f n) ≫
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve (F.obj ∘ U))
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (F.obj ∘ U)) P).hom.f n =
      (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve U)
        (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (F.op ⋙ P)).hom.f n ≫
          (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U (P ⋙ G)).hom.f n
  rw [GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f, GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f, hom_f, hom_f]
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map G
    (fun t : Fin (n + 1) → ι => P.map (PreservesProduct.iso F (U ∘ t)).inv.op)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductCoefficient.NonemptyCechProductCoefficient
