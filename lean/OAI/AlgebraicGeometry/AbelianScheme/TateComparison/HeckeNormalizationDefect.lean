import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GenericComponents
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComponentConstantFactorization

/-! # Hecke Normalization Defect -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! The difference between the actual trace and the induced Albanese
endomorphism is a map through the constant group of K-rational points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem HeckeNormalizationDefect.div_div_exchange {G : Type*} [CommGroup G] {a b c d : G}
    (h : a / b = c / d) : a / c = b / d := by
  apply div_eq_div_iff_mul_eq_mul.mpr
  exact (div_eq_div_iff_mul_eq_mul.mp h).trans (mul_comm c b)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.HeckeNormalizationDefect_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.HeckeNormalizationDefect_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm

def Data.SphericalPELAlbaneseData.heckeNormalizationDefect (t : Local.IntegralType s) : D.space ⟶ D.albaneseGroup.X :=
  (D.albaneseMap hg ≫ End.endSchemeMap D.albaneseGroup.X (D.heckeEnd hg t)) /
    D.albaneseTrace hg t

theorem Data.SphericalPELAlbaneseData.heckeNormalizationDefect_component (t : Local.IntegralType s) (j : Fin D.componentCount) :
    D.componentInclusion j ≫ D.heckeNormalizationDefect hg t =
      toUnit (D.componentGeneric j) ≫ D.genericComponentBasePoint j ≫
        D.componentInclusion j ≫ D.heckeNormalizationDefect hg t := by
  have h := D.heckeEnd_differences hg t j (𝟙 (D.componentGeneric j))
    (toUnit (D.componentGeneric j) ≫ D.genericComponentBasePoint j)
  simp only [Category.id_comp, GrpObj.div_comp, Category.assoc] at h
  have he := HeckeNormalizationDefect.div_div_exchange h
  simpa only [Data.SphericalPELAlbaneseData.heckeNormalizationDefect, GrpObj.comp_div, Category.assoc] using he

theorem Data.SphericalPELAlbaneseData.heckeNormalizationDefect_constant (t : Local.IntegralType s) :
    ComponentConstantFactorization.FactorsThroughConstantGroup (D.heckeNormalizationDefect hg t) := by
  apply ComponentConstantFactorization.factorsThroughConstantGroup_of_components D.componentGeneric (D.genericComponentIso hg)
    (D.heckeNormalizationDefect hg t)
    (fun j => D.genericComponentBasePoint j ≫ D.componentInclusion j ≫ D.heckeNormalizationDefect hg t)
  intro j
  rw [← Category.assoc, D.genericComponentIso_ι hg]
  exact D.heckeNormalizationDefect_component hg t j

theorem Data.SphericalPELAlbaneseData.trace_heckeNormalizationDefect_differences (u v : Local.IntegralType s)
    (j : Fin D.componentCount) {T : Over (Spec (.of K))} (x y : T ⟶ D.componentGeneric j) :
    letI := D.genericSpace_reduced hg
    letI := D.genericSpace_locallyNoetherian hg
    letI := D.albaneseGroup_separated hg
    x ≫ D.componentInclusion j ≫
      (D.correspondence u).algebraicTrace (D.heckeNormalizationDefect hg v) =
    y ≫ D.componentInclusion j ≫
      (D.correspondence u).algebraicTrace (D.heckeNormalizationDefect hg v) := by
  have : IsReduced D.space.left := D.genericSpace_reduced hg
  have : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian hg
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hg
  have : PreconnectedSpace (D.componentGeneric j).left := D.genericComponent_preconnected hg j
  exact ((D.heckeNormalizationDefect_constant hg v).trace (D.correspondence u)).differences
    (D.componentInclusion j) x y

end

/-! Composing the induced endomorphism with a trace agrees on component
differences with the actual iterated correspondence trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.HeckeTraceComposition_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.HeckeTraceComposition_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm

theorem Data.SphericalPELAlbaneseData.heckeEnd_trace_differences (u v : Local.IntegralType s) (j : Fin D.componentCount)
    {T : Over (Spec (.of K))} (x y : T ⟶ D.componentGeneric j) :
    letI := D.genericSpace_reduced hg
    letI := D.genericSpace_locallyNoetherian hg
    letI := D.albaneseGroup_separated hg
    ((x ≫ D.componentInclusion j ≫ D.albaneseTrace hg u) /
      (y ≫ D.componentInclusion j ≫ D.albaneseTrace hg u)) ≫
        End.endSchemeMap D.albaneseGroup.X (D.heckeEnd hg v) =
      (x ≫ D.componentInclusion j ≫ (D.correspondence u).algebraicTrace (D.albaneseTrace hg v)) /
        (y ≫ D.componentInclusion j ≫ (D.correspondence u).algebraicTrace (D.albaneseTrace hg v)) := by
  have : IsReduced D.space.left := D.genericSpace_reduced hg
  have : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian hg
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hg
  have h := D.trace_heckeNormalizationDefect_differences hg u v j x y
  simp only [Data.SphericalPELAlbaneseData.heckeNormalizationDefect, Correspondences.EtaleCorrespondence.algebraicTrace_div,
    Correspondences.EtaleCorrespondence.algebraicTrace_postcomp, GrpObj.comp_div] at h
  have he := HeckeNormalizationDefect.div_div_exchange h
  simpa only [GrpObj.div_comp, Category.assoc, Data.SphericalPELAlbaneseData.albaneseTrace] using he

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
