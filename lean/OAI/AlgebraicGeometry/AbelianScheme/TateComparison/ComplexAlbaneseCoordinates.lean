import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseBaseChangeComp
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteAlbaneseFactor

/-! # Complex Albanese Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! The actual complex total Albanese projects to its original component
Albanese groups through the canonical iterated-base-change comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)

local instance Data.SphericalPELAlbaneseData.ComplexAlbaneseProjections_local1 : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.ComplexAlbaneseProjections_local2 : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

def Data.SphericalPELAlbaneseData.complexAlbaneseProjection (j : Fin D.componentCount) :
    D.complexAlbanese.X ⟶ (D.components.complexAbelian D.complexPoint j).X :=
  (AlbaneseBaseChangeComp.pullbackCompositionIso (Products.componentProduct D.components.A).X D.complexGenericPoint D.generic).inv ≫
    (Over.pullback D.complexPoint).map (Products.componentProductProjection D.components.A j)

instance Data.SphericalPELAlbaneseData.complexAlbaneseProjection_isMonHom (j : Fin D.componentCount) :
    IsMonHom (D.complexAlbaneseProjection j) := by
  unfold Data.SphericalPELAlbaneseData.complexAlbaneseProjection
  infer_instance

theorem Data.SphericalPELAlbaneseData.complexAlbaneseProjection_eq (j : Fin D.componentCount) :
    D.complexAlbaneseProjection j =
      (Over.pullbackComp D.complexGenericPoint D.generic).inv.app (Products.componentProduct D.components.A).X ≫
        (Over.pullback D.complexPoint).map (Products.componentProductProjection D.components.A j) := by
  rw [Data.SphericalPELAlbaneseData.complexAlbaneseProjection, AlbaneseBaseChangeComp.pullbackCompositionIso_inv]

end

/-! The actual complex component maps have exactly one nonzero Albanese
coordinate, through the canonical base-change comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def Data.SphericalPELAlbaneseData.complexSourceInclusion (j : Fin D.componentCount) :
    D.components.complexSurface D.complexPoint j ⟶ D.complexSpace :=
  (Over.pullbackComp D.complexGenericPoint D.generic).hom.app (D.components.S j) ≫
    (Over.pullback D.complexGenericPoint).map ((Over.pullback D.generic).map (D.inclusion j))

theorem Data.SphericalPELAlbaneseData.complexAlbanese_component_coordinate (j k : Fin D.componentCount) :
    D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg ≫ D.complexAlbaneseProjection k =
      (Over.pullback D.complexPoint).map (D.components.coordinateMap j k) := by
  have : IsIso D.componentAssembly := hg.decomposition
  let a := D.components.totalMap (asIso D.componentAssembly) ≫
    (Products.componentProductComparison D.components.A).inv
  let F := Over.pullback D.generic ⋙ Over.pullback D.complexGenericPoint
  let F₀ := Over.pullback D.complexPoint
  let e := Over.pullbackComp D.complexGenericPoint D.generic
  let r := D.inclusion j ≫ a
  have hr : r ≫ Products.componentProductProjection D.components.A k = D.components.coordinateMap j k := by
    change (D.inclusion j ≫ (D.components.totalMap (asIso D.componentAssembly) ≫
      (Products.componentProductComparison D.components.A).inv)) ≫ Products.componentProductProjection D.components.A k = _
    rw [Category.assoc, Category.assoc, CentralAction.AlbaneseCoordinates.Construction.componentProductComparison_inv_projection]
    have h := D.components.totalMap_coordinate (asIso D.componentAssembly) j k
    simpa only [asIso_hom, Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc_assoc] using h
  rw [D.complexAlbaneseProjection_eq]
  change (e.hom.app (D.components.S j) ≫ F.map (D.inclusion j)) ≫
    F.map a ≫ e.inv.app (Products.componentProduct D.components.A).X ≫
      F₀.map (Products.componentProductProjection D.components.A k) = _
  calc
    _ = (e.hom.app (D.components.S j) ≫ F.map r ≫ e.inv.app (Products.componentProduct D.components.A).X) ≫
        F₀.map (Products.componentProductProjection D.components.A k) := by
      simp only [r, Functor.map_comp, Category.assoc]
    _ = F₀.map r ≫ F₀.map (Products.componentProductProjection D.components.A k) := by
      rw [NatIso.naturality_2]
    _ = F₀.map (r ≫ Products.componentProductProjection D.components.A k) := (F₀.map_comp _ _).symm
    _ = F₀.map (D.components.coordinateMap j k) := congrArg F₀.map hr

theorem Data.SphericalPELAlbaneseData.complexAlbanese_component_self (j : Fin D.componentCount) :
    D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg ≫ D.complexAlbaneseProjection j =
      D.components.complexMap D.complexPoint j := by
  rw [D.complexAlbanese_component_coordinate hg, PELModuli.IntegralModel.Components.ComponentAlbaneseData.coordinateMap_self]
  rfl

theorem Data.SphericalPELAlbaneseData.complexAlbanese_component_ne (j k : Fin D.componentCount) (hjk : j ≠ k) :
    D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg ≫ D.complexAlbaneseProjection k = 1 := by
  rw [D.complexAlbanese_component_coordinate hg, D.components.coordinateMap_ne j k hjk,
    Functor.map_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
