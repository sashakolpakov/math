import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal

/-! # Total Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.TotalCoordinates

noncomputable section

/-! Summand and section coordinates for the genuine coefficient
comparison on the original finite Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial _root_.HomologicalComplex₂

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I) (P : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E P
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E
  (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P)

theorem injection (p q n : ℕ) (h : p+q=n) :
    F.map ((K).ιTotal (.up ℕ) p q n h) ≫
      (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE P).hom.f n =
        ((GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE P).hom.f p).f q ≫
          (L).ιTotal (.up ℕ) p q n h := by
  change F.map ((K).ιTotal (.up ℕ) p q n h) ≫
    ((AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).inv.f n ≫
      (total.map (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE P).hom (.up ℕ)).f n) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (total.map (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE P).hom
      (.up ℕ)).f n) (IntegralComparison.Finite.TotalCoefficientCoordinates.injection F K p q n h)).trans
        ((AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal_map L
          (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE P).hom (.up ℕ) p q n h))

omit [HasCoproducts A] [HasCoproducts B] in
theorem component_projection (p q : ℕ) (t : (E.obj (op ⦋q⦌)).I) :
    ((GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE P).hom.f p).f q ≫
      Pi.π (fun i => F.obj ((P.X p).obj (op ((E.obj (op ⦋q⦌)).obj i)))) t =
        F.map (Pi.π (fun i => (P.X p).obj (op ((E.obj (op ⦋q⦌)).obj i))) t) := by
  change (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso F E hE (P.X p)).hom.f q ≫ _ = _
  rw [GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  exact piComparison_comp_π _ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.TotalCoordinates
