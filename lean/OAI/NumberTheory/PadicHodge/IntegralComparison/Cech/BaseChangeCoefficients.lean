import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Base Change Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeCoefficients

noncomputable section

/-! Inverse-image Čech comparison commutes with the actual
product-preserving change of coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
universe w v vD vA vB u uD uA uB
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{w} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{w,w} G]
  {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteLimits F] {ι : Type w} (U : ι → C) (P : Dᵒᵖ ⥤ A)

theorem naturality :
    (G.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι (F.obj ∘ U)).cech P).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech (F.op ⋙ P)).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (P ⋙ G)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change G.map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).hom.f n) ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι (F.obj ∘ U)).cech P).hom.f n =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech (F.op ⋙ P)).hom.f n ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (P ⋙ G)).hom.f n
  rw [AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f, AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f]
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map G
    (fun t : Fin (n + 1) → ι =>
      P.map (PreservesProduct.iso F (U ∘ t)).symm.op.hom)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeCoefficients
