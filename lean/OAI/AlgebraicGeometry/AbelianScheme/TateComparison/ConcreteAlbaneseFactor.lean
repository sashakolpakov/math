import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseReference

/-! # Concrete Albanese Factor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The supplied complex Albanese universal property factors actual maps
into the complete, now projectively presented, Albanese group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.ActualAlbaneseFactor_local1 : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.ActualAlbaneseFactor_local2 : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

def Data.SphericalPELAlbaneseData.normalizedComplexComponentMap (j : Fin D.componentCount)
    (f : D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X) :
    D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X :=
  f / (toUnit (D.components.complexSurface D.complexPoint j) ≫
    D.components.complexBasePoint D.complexPoint j ≫ f)

theorem Data.SphericalPELAlbaneseData.normalizedComplexComponentMap_point (j : Fin D.componentCount)
    (f : D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X) :
    D.components.complexBasePoint D.complexPoint j ≫ D.normalizedComplexComponentMap j f = 1 := by
  simp only [Data.SphericalPELAlbaneseData.normalizedComplexComponentMap, GrpObj.comp_div, ← Category.assoc,
    comp_toUnit, toUnit_unit, Category.id_comp, div_self']

include hg in
theorem Data.SphericalPELAlbaneseData.complexComponentFactor_exists (j : Fin D.componentCount)
    (f : D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X) :
    ∃! φ : (D.components.complexAbelian D.complexPoint j).X ⟶ D.complexAlbanese.X,
      IsMonHom φ ∧ D.components.complexMap D.complexPoint j ≫ φ =
        D.normalizedComplexComponentMap j f :=
  (hg.albanese j).2 (D.actualComplexAlbaneseVariety hg) (D.normalizedComplexComponentMap j f)
    (D.normalizedComplexComponentMap_point j f)

def Data.SphericalPELAlbaneseData.complexComponentFactor (j : Fin D.componentCount)
    (f : D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X) :
    (D.components.complexAbelian D.complexPoint j).X ⟶ D.complexAlbanese.X :=
  (D.complexComponentFactor_exists hg j f).choose

instance Data.SphericalPELAlbaneseData.complexComponentFactor_isMonHom (j : Fin D.componentCount)
    (f : D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X) :
    IsMonHom (D.complexComponentFactor hg j f) :=
  (D.complexComponentFactor_exists hg j f).choose_spec.1.1

theorem Data.SphericalPELAlbaneseData.complexComponentFactor_equation (j : Fin D.componentCount)
    (f : D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X) :
    D.components.complexMap D.complexPoint j ≫ D.complexComponentFactor hg j f =
      D.normalizedComplexComponentMap j f :=
  (D.complexComponentFactor_exists hg j f).choose_spec.1.2

theorem Data.SphericalPELAlbaneseData.complexComponentFactor_differences (j : Fin D.componentCount)
    (f : D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X)
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (x y : T ⟶ D.components.complexSurface D.complexPoint j) :
    ((x ≫ D.components.complexMap D.complexPoint j) /
      (y ≫ D.components.complexMap D.complexPoint j)) ≫ D.complexComponentFactor hg j f =
        (x ≫ f) / (y ≫ f) := by
  rw [GrpObj.div_comp, Category.assoc, Category.assoc, D.complexComponentFactor_equation hg j f]
  have hunit : x ≫ toUnit (D.components.complexSurface D.complexPoint j) =
      y ≫ toUnit (D.components.complexSurface D.complexPoint j) :=
    Over.mkIdTerminal.hom_ext _ _
  simp only [Data.SphericalPELAlbaneseData.normalizedComplexComponentMap, GrpObj.comp_div]
  rw [← Category.assoc x, ← Category.assoc y, hunit]
  exact div_div_div_cancel_right _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
