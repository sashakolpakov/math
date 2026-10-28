import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexHeckePointIndependence
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldCoverPointAction

/-! # Hecke End Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Descent of the constructed complex Hecke endomorphisms to actual
integral algebraic endomorphisms over the given number field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.HeckeEndDescent_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.HeckeEndDescent_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm
local instance Data.SphericalPELAlbaneseData.HeckeEndDescent_local3 : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.HeckeEndDescent_local4 : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

theorem Data.SphericalPELAlbaneseData.complexHeckeEnd_geometric_compatibility (t : Local.IntegralType s)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (b : Spec (.of Ω) ⟶ Spec (.of K))
    (x y : Over.mk b ⟶ FieldGeometricDescent.fieldSource D.complexGenericPoint D.albaneseGroup.X)
    (hxy : x ≫ FieldGeometricDescent.fieldSourceProjection D.complexGenericPoint D.albaneseGroup.X =
      y ≫ FieldGeometricDescent.fieldSourceProjection D.complexGenericPoint D.albaneseGroup.X) :
    x ≫ IntegralFieldDescent.fieldEndUnderlying D.complexGenericPoint D.albaneseGroup.X
      (End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t)) =
    y ≫ IntegralFieldDescent.fieldEndUnderlying D.complexGenericPoint D.albaneseGroup.X
      (End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t)) := by
  have he := D.complexHeckePointEnd_independent hg t b
    (FieldCoverPointAction.fieldCoverPointToBase D.complexGenericPoint D.albaneseGroup.X x)
    (FieldCoverPointAction.fieldCoverPointToBase D.complexGenericPoint D.albaneseGroup.X y)
    (FieldCoverPointAction.fieldCoverPointToBase_comp D.complexGenericPoint D.albaneseGroup.X x)
    (FieldCoverPointAction.fieldCoverPointToBase_comp D.complexGenericPoint D.albaneseGroup.X y)
  apply Additive.ofMul.injective
  rw [← FieldCoverPointAction.fieldEndUnderlying_point_action D.complexGenericPoint D.albaneseGroup.X x,
    ← FieldCoverPointAction.fieldEndUnderlying_point_action D.complexGenericPoint D.albaneseGroup.X y]
  change D.complexHeckePointEnd hg t b _ _ (Additive.ofMul _) =
    D.complexHeckePointEnd hg t b _ _ (Additive.ofMul _)
  rw [he, hxy]

theorem Data.SphericalPELAlbaneseData.heckeEnd_exists (t : Local.IntegralType s) :
    ∃ a : D.EndK, BaseChange.endBaseChange D.albaneseGroup.X D.complexGenericPoint a =
      D.complexHeckeEnd hg t := by
  have : IsIntegral (pullback D.albaneseGroup.X.hom D.complexGenericPoint) :=
    (D.actualComplexAlbaneseVariety hg).variety.property
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hg
  obtain ⟨a, ha⟩ := IntegralFieldDescent.integralEnd_descends_of_geometric_compatibility
    D.complexGenericPoint D.albaneseGroup.X
    (End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t))
    (fun Ω _ _ b x y hxy => D.complexHeckeEnd_geometric_compatibility hg t b x y hxy)
  refine ⟨a, ha.trans ?_⟩
  apply End.endSchemeMap_injective D.complexAlbanese.X
  rw [End.endSchemeMap_ofSchemeMap]

def Data.SphericalPELAlbaneseData.heckeEnd (t : Local.IntegralType s) : D.EndK := (D.heckeEnd_exists hg t).choose

theorem Data.SphericalPELAlbaneseData.heckeEnd_baseChange (t : Local.IntegralType s) :
    BaseChange.endBaseChange D.albaneseGroup.X D.complexGenericPoint (D.heckeEnd hg t) =
      D.complexHeckeEnd hg t := (D.heckeEnd_exists hg t).choose_spec

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
