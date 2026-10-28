import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.RefinementCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientNaturality

/-! # Refinement Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient

noncomputable section

/-! Additive coefficient change commutes with refinement of the
original Cech bicomplex and total of a presheaf complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b d e
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι κ : Type} [Finite ι] [Finite κ]
  (U : ι → C) (V : κ → C) (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

local notation "EU" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "EV" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V

def bicomplexMap : CoefficientTotal.CechPresheafCoefficientTotal.bicomplex EU K ⟶ CoefficientTotal.CechPresheafCoefficientTotal.bicomplex EV K :=
  ((NonemptyCech.Refinement.NonemptyCechRefinement.transformation U V r).mapHomologicalComplex (.up ℕ)).app K

def map := HomologicalComplex₂.total.map (bicomplexMap U V r K) (.up ℕ)

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F (bicomplexMap U V r K) ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F EV (NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient.finite_indices V) K).hom =
      (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F EU (NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient.finite_indices U) K).hom ≫
        bicomplexMap U V r (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F K) := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient.natural F U V r (K.X q)

theorem total : (F.mapHomologicalComplex (.up ℕ)).map (CechPresheafRefinementCoefficient.map U V r K) ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.totalIso F EV (NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient.finite_indices V) K).hom =
      (CoefficientTotal.CechPresheafCoefficientTotal.totalIso F EU (NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient.finite_indices U) K).hom ≫
        CechPresheafRefinementCoefficient.map U V r (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F K) := by
  let a := bicomplexMap U V r K
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex EU K))
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex EV K))
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F a) (.up ℕ))
    ((F.mapHomologicalComplex (.up ℕ)).map (CechPresheafRefinementCoefficient.map U V r K))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural F a)
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := (T.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap F a)
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F EV (NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient.finite_indices V) K).hom).symm.trans
      ((congrArg T.map (bicomplex F U V r K)).trans
        (T.map_comp (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F EU (NonemptyCech.RefinementCoefficient.NonemptyCechRefinementCoefficient.finite_indices U) K).hom
          (bicomplexMap U V r (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F K))))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient
