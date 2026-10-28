import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalCoefficient

/-! # Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Coefficient.CechAssemblyCoefficientHodge

noncomputable section

/-! The original assembled-Cech coefficient isomorphism is the
actual bicomplex coefficient comparison, so its Hodge square is available. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (Opposite.op n)).I) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F
    (CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)) ≅
      CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E
        (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (P ⋙ F.mapHomologicalComplex (.up ℕ))) :=
  CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P) ≪≫
    ((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).mapIso
      (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F P).symm

theorem iso_eq : CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P =
    NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso F (bicomplexIso F E hE P) := by
  apply Iso.ext
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  let a := (CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)).hom
  let b := (((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).mapIso
    (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F P).symm).hom
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q => (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F
      (CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P))).inv ≫ q)
        (T.map_comp a b).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Coefficient.CechAssemblyCoefficientHodge
