import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralObject
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ShiftedHom

/-! # Spectral Connecting -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralConnecting

noncomputable section

/-! Native formulas for the connecting maps of the filtered tensor
spectral object. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.ComposableArrows _root_.CochainComplex

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)
  {ι : Type*} [Category* ι] (D : ι ⥤ CochainComplex (ModuleCat.{0} R) ℤ)
  {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

theorem precomp_δ :
    ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} R)).precomp D).δ f g =
      _root_.CategoryTheory.ShiftedHom.map (mappingConeCompTriangle (D.map f) (D.map g)).mor₃
        (HomotopyCategory.quotient _ _) := by
  change (HomotopyCategory.quotient _ _).map
      (mappingCone.map (D.map g) (D.map g) (𝟙 _) (𝟙 _) (by simp)) ≫
    ((HomotopyCategory.quotient _ _).mapTriangle.obj
      (mappingConeCompTriangle (D.map f) (D.map g))).mor₃ ≫
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{0} R) (.up ℤ)) (1 : ℤ)).map
      ((HomotopyCategory.quotient _ _).map
        (mappingCone.map (D.map f) (D.map f) (𝟙 _) (𝟙 _) (by simp))) = _
  simp only [mappingCone.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  change _root_.CategoryTheory.ShiftedHom.map (mappingConeCompTriangle (D.map f) (D.map g)).mor₃
      (HomotopyCategory.quotient _ _) ≫
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{0} R) (.up ℤ)) (1 : ℤ)).map
      ((HomotopyCategory.quotient _ _).map (𝟙 (mappingConeCompTriangle (D.map f) (D.map g)).obj₁)) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

theorem triangulated_δ :
    (Tensor.SpectralObject.triangulated R K D).δ f g =
      _root_.CategoryTheory.ShiftedHom.map
        (_root_.CategoryTheory.ShiftedHom.map (mappingConeCompTriangle (D.map f) (D.map g)).mor₃
          (Homotopy.complexFunctor R K))
        (HomotopyCategory.quotient _ _) := by
  change (((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} R)).precomp D).mapTriangulatedFunctor
    (Homotopy.homotopyFunctor R K)).δ f g = _
  rw [Triangulated.SpectralObject.mapTriangulatedFunctor_δ, precomp_δ]
  exact Tensor.ShiftedHom.map R K _

@[reassoc]
theorem abelian_δ (n m : ℤ) (h : n + 1 = m) :
    (Tensor.SpectralObject.abelian R K D).δ f g n m h ≫
        (Tensor.SpectralObject.termIso R K D f m).hom =
      (Tensor.SpectralObject.termIso R K D g n).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0).shiftMap
          (_root_.CategoryTheory.ShiftedHom.map (mappingConeCompTriangle (D.map f) (D.map g)).mor₃
            (Homotopy.complexFunctor R K)) n m (by omega) := by
  change (HomotopyCategory.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0).shiftMap
    ((Tensor.SpectralObject.triangulated R K D).δ f g) n m (by omega) ≫ _ = _
  rw [triangulated_δ, HomotopyCategory.homologyFunctor_shiftMap]
  simp only [Tensor.SpectralObject.termIso, Iso.app_hom, Category.assoc]
  change (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} R) (.up ℤ) n).hom.app
      ((Homotopy.complexFunctor R K).obj (mappingCone (D.map g))) ≫ _ ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} R) (.up ℤ) m).inv.app
      ((Homotopy.complexFunctor R K).obj (mappingCone (D.map f))) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} R) (.up ℤ) m).hom.app
      ((Homotopy.complexFunctor R K).obj (mappingCone (D.map f))) = _
  rw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralConnecting
