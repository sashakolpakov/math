import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientTotal

/-! # Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientCoordinates.CechAssemblyCoefficientCoordinates

noncomputable section

/-! The assembly coordinate isomorphism is strict, so the original
assembled coefficient comparison has the presheaf comparison as its map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

theorem hom : (CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P).hom =
    (CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)).hom := by
  let T := (FormalCoproduct.cochainComplexFunctor (A := B) E).mapHomologicalComplex (.up ℕ)
  change (CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)).hom ≫
    HomologicalComplex₂.total.map (T.map (𝟙 _)) (.up ℕ) = _
  rw [T.map_id, HomologicalComplex₂.total.map_id]
  exact Category.comp_id _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientCoordinates.CechAssemblyCoefficientCoordinates
