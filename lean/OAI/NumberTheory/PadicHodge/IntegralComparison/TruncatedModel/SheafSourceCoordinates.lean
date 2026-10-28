import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafGlobalData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechCoefficientUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientComposition

/-! # Sheaf Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafSourceCoordinates

noncomputable section

/-! The actual ordinary global coordinates and sheaf unit reduce to
the canonical coefficient map on the unchanged native small cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uA vA uB vB uD vD
private theorem composite_input
    {C : Type u} [Category.{v} C]
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (E : SimplicialObject (FormalCoproduct.{0} C))
    (hE : ∀ q, Finite (E.obj (Opposite.op q)).I)
    (P : Cᵒᵖ ⥤ CochainComplex A ℕ) {L : CochainComplex A ℕ}
    (a : L ⟶ GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E P) :
    (G.mapHomologicalComplex (.up ℕ)).map
        ((F.mapHomologicalComplex (.up ℕ)).map a ≫
          (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P).hom) ≫
      (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E hE
        (P ⋙ F.mapHomologicalComplex (.up ℕ))).hom =
    ((F ⋙ G).mapHomologicalComplex (.up ℕ)).map a ≫
      (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso (F ⋙ G) E hE
        (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)).hom := by
  have h := congrArg
    (fun t => (G.mapHomologicalComplex (.up ℕ)).map
      ((F.mapHomologicalComplex (.up ℕ)).map a) ≫ t)
    (GeometricComparison.CechPresheaf.CoefficientComposition.CechPresheafCoefficientComposition.hom F G E hE (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P))
  simp only [Functor.map_comp, GeometricComparison.CechAssembly.CoefficientCoordinates.CechAssemblyCoefficientCoordinates.hom, Category.assoc]
  exact h

private theorem inv_prefix {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (a : A ⟶ D) (b : B ⟶ D) (h : e.hom ≫ b = a) : e.inv ≫ a = b := by
  rw [← h, Iso.inv_hom_id_assoc]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

abbrev nativeCoordinates := Small.OrdinaryCechCoefficientUnit.Ordinary.targetCoordinates
  (Truncated.Witt.Ring p k n) X (OrdinarySectionMap.Ordinary.coefficients p k n)

abbrev sourceProductIso := Small.OrdinaryCechCoefficientUnit.Ordinary.targetProductIso
  (Truncated.Witt.Ring p k n) X (OrdinarySectionMap.Ordinary.coefficients p k n)

omit [Fintype k] [CharP k p] in
theorem combined_coordinates : (OrdinaryGlobal.OrdinaryComparison.coordinates p k n X).hom =
    ((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).map
        (Small.OrdinaryCechTotal.Ordinary.totalIso (Truncated.Witt.Ring p k n) X).inv ≫
      (Small.OrdinaryCechCoefficientUnit.Ordinary.sourceCoordinates (Truncated.Witt.Ring p k n) X
        (OrdinarySectionMap.Ordinary.coefficients p k n)).hom := by
  dsimp only [OrdinaryGlobal.OrdinaryComparison.coordinates,
    OrdinaryAssemblyCoordinates.Ordinary.sourceIso,
    OrdinaryCechCoordinates.Ordinary.iso]
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom]
  exact composite_input
    (ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n)))
    (Principal.Comparison.coefficients p k)
    (NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X))
    (Small.OrdinaryCechTotal.Ordinary.finiteIndices (Truncated.Witt.Ring p k n) X)
    (Small.OrdinaryCechTotal.Ordinary.diagram (Truncated.Witt.Ring p k n) X)
    (Small.OrdinaryCechTotal.Ordinary.totalIso (Truncated.Witt.Ring p k n) X).inv

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
theorem unit_eq : SheafGlobalData.Comparison.unit p k n X =
    Small.OrdinaryCechCoefficientUnit.Ordinary.mappedUnit (Truncated.Witt.Ring p k n) X
      (OrdinarySectionMap.Ordinary.coefficients p k n) := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

omit [Fintype k] [CharP k p] in
theorem total_unit : SheafGlobalData.Comparison.totalUnit p k n X =
    (Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal (Truncated.Witt.Ring p k n) X).map
      (Small.OrdinaryCechCoefficientUnit.Ordinary.mappedUnit (Truncated.Witt.Ring p k n) X
        (OrdinarySectionMap.Ordinary.coefficients p k n)) := by
  unfold SheafGlobalData.Comparison.totalUnit
  rw [unit_eq]
  rfl

omit [Fintype k] [CharP k p] in
theorem comparison :
    (OrdinaryGlobal.OrdinaryComparison.coordinates p k n X).hom ≫
      SheafGlobalData.Comparison.totalUnit p k n X ≫
        (sourceProductIso p k n X).hom = (nativeCoordinates p k n X).hom := by
  rw [combined_coordinates, total_unit]
  have h := inv_prefix
    (((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).mapIso
      (Small.OrdinaryCechTotal.Ordinary.totalIso (Truncated.Witt.Ring p k n) X))
    _ _ (Small.OrdinaryCechCoefficientUnit.Ordinary.comparison (Truncated.Witt.Ring p k n) X
      (OrdinarySectionMap.Ordinary.coefficients p k n))
  simpa only [Functor.mapIso_inv, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafSourceCoordinates
