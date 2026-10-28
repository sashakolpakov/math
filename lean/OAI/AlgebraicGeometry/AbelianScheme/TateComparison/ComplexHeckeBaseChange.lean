import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexAlbaneseEnd
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PointedMapNormalization

/-! # Complex Hecke Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! The constructed integral complex Hecke endomorphisms act on every
component difference by the actual algebraic trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.ComplexHeckeDifferences_local1 : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.ComplexHeckeDifferences_local2 : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

theorem Data.SphericalPELAlbaneseData.complexHeckeEnd_point_differences (t : Local.IntegralType s) (j : Fin D.componentCount)
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (x y : T ⟶ D.components.complexSurface D.complexPoint j) :
    ((x ≫ D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg) /
      (y ≫ D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg)) ≫
        End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t) =
      (x ≫ D.complexSourceInclusion j ≫
        (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t)) /
      (y ≫ D.complexSourceInclusion j ≫
        (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t)) := by
  simp only [GrpObj.div_comp, Category.assoc, D.complexHeckeEnd_component hg t j]
  exact PointedMapNormalization.normalizedMap_point_differences
    (D.complexSourceInclusion j ≫ (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t))
    (D.components.complexBasePoint D.complexPoint j ≫ D.complexSourceInclusion j ≫
      (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t)) x y

end

/-! The complex Hecke difference equation expressed on the literal
base changes of the generic component schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.ComplexHeckeBaseChange_local1 : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.ComplexHeckeBaseChange_local2 : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

theorem Data.SphericalPELAlbaneseData.complexHeckeEnd_baseChange_differences (t : Local.IntegralType s) (j : Fin D.componentCount)
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y : T ⟶ (Over.pullback D.complexGenericPoint).obj (D.componentGeneric j)) :
    ((x ≫ (Over.pullback D.complexGenericPoint).map
        (D.componentInclusion j ≫ D.albaneseMap hg)) /
      (y ≫ (Over.pullback D.complexGenericPoint).map
        (D.componentInclusion j ≫ D.albaneseMap hg))) ≫
        End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t) =
      (x ≫ (Over.pullback D.complexGenericPoint).map
        (D.componentInclusion j ≫ D.albaneseTrace hg t)) /
      (y ≫ (Over.pullback D.complexGenericPoint).map
        (D.componentInclusion j ≫ D.albaneseTrace hg t)) := by
  let e := Over.pullbackComp D.complexGenericPoint D.generic
  have he (z : T ⟶ (Over.pullback D.complexGenericPoint).obj (D.componentGeneric j)) :
      (z ≫ e.inv.app (D.components.S j)) ≫ D.complexSourceInclusion j =
        z ≫ (Over.pullback D.complexGenericPoint).map (D.componentInclusion j) := by
    change (z ≫ e.inv.app (D.components.S j)) ≫
      (e.hom.app (D.components.S j) ≫ _) = _
    simp only [Category.assoc, e.inv_hom_id_app_assoc]
  have h := D.complexHeckeEnd_point_differences hg t j
    (x ≫ e.inv.app (D.components.S j)) (y ≫ e.inv.app (D.components.S j))
  simpa only [← Category.assoc, he, Functor.map_comp] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
