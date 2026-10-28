import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsPrimitive
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexComponentCover
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsAffineLocality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeEndPoints

/-! # Hecke Forms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual integral Albanese Hecke maps satisfy the branch-trace
identity on every affine test algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.HeckeForms_group : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.HeckeForms_comm : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

include hg in
theorem Data.SphericalPELAlbaneseData.complexAlbanese_oneForm_primitive (ω : D.OneFormsA) : PrimitiveFormTrace.IsPrimitiveOneForm ω :=
  FormsPrimitive.abelian_oneForm_primitive (D.actualComplexAlbaneseVariety hg) ω

theorem Data.SphericalPELAlbaneseData.heckeEnd_forms_trace (t : Local.IntegralType s) (ω : D.OneFormsA) :
    D.albanesePullback hg (D.pullbackForms (D.heckeEnd hg t) ω) =
      FormConstants.formsPullback ((Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t)) ω := by
  apply FormsAffineLocality.formsPullback_openCover_injective
    (D.components.complexSurface D.complexPoint) D.complexSourceInclusion
    (D.complexSourceInclusion_open hg) (D.complexSourceInclusion_cover hg)
  intro j
  apply Subtype.ext
  funext R z
  change ω.val R (z ≫ D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg ≫
    (Over.pullback D.complexGenericPoint).map (End.endSchemeMap D.albaneseGroup.X (D.heckeEnd hg t))) =
      ω.val R (z ≫ D.complexSourceInclusion j ≫
        (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t))
  rw [D.heckeEnd_schemeMap_baseChange hg, D.complexHeckeEnd_component hg]
  simp only [Data.SphericalPELAlbaneseData.normalizedComplexComponentMap, GrpObj.comp_div]
  simpa only [Category.assoc] using PrimitiveFormTrace.primitiveForm_constant_translate ω (D.complexAlbanese_oneForm_primitive hg ω)
    (D.components.complexBasePoint D.complexPoint j ≫ D.complexSourceInclusion j ≫
      (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t)) R
    (z ≫ D.complexSourceInclusion j ≫
      (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t))
    (z ≫ toUnit (D.components.complexSurface D.complexPoint j))

theorem Data.SphericalPELAlbaneseData.complexAlbaneseTrace_baseChange (t : Local.IntegralType s) :
    letI : Smooth D.complexSpace.hom :=
      letI : Smooth D.space.hom := D.genericSpace_smooth hg
      inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.space.hom D.complexGenericPoint))
    letI : IsReduced D.complexSpace.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.complexSpace.hom
    letI : IsLocallyNoetherian D.complexSpace.left := LocallyOfFiniteType.isLocallyNoetherian D.complexSpace.hom
    letI : IsSeparated D.complexAlbanese.X.hom :=
      letI : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hg
      inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd D.albaneseGroup.X.hom D.complexGenericPoint))
    (D.complexCorrespondence t).algebraicTrace (D.complexAlbaneseMap hg) =
      (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t) := by
  have : Smooth D.space.hom := D.genericSpace_smooth hg
  have : Smooth D.complexSpace.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.space.hom D.complexGenericPoint))
  have : IsReduced D.complexSpace.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.complexSpace.hom
  have : IsLocallyNoetherian D.complexSpace.left := LocallyOfFiniteType.isLocallyNoetherian D.complexSpace.hom
  have : IsReduced D.space.left := D.genericSpace_reduced hg
  have : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian hg
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hg
  have : IsSeparated D.complexAlbanese.X.hom :=
    inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd D.albaneseGroup.X.hom D.complexGenericPoint))
  exact (D.correspondence t).algebraicTrace_baseChange D.complexGenericPoint (D.albaneseMap hg)

theorem Data.SphericalPELAlbaneseData.heckeEnd_branchTrace (t : Local.IntegralType s) (ω : D.OneFormsA) :
    Branches.IsBranchTrace (D.complexCorrespondence t) (D.albanesePullback hg ω)
      (D.albanesePullback hg (D.pullbackForms (D.heckeEnd hg t) ω)) := by
  have : Smooth D.space.hom := D.genericSpace_smooth hg
  have : Smooth D.complexSpace.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.space.hom D.complexGenericPoint))
  have : IsReduced D.complexSpace.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.complexSpace.hom
  have : IsLocallyNoetherian D.complexSpace.left := LocallyOfFiniteType.isLocallyNoetherian D.complexSpace.hom
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hg
  have : IsSeparated D.complexAlbanese.X.hom :=
    inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd D.albaneseGroup.X.hom D.complexGenericPoint))
  rw [D.heckeEnd_forms_trace hg, ← D.complexAlbaneseTrace_baseChange hg]
  exact (D.complexCorrespondence t).algebraicTrace_primitiveForm (D.complexAlbaneseMap hg) ω
    (D.complexAlbanese_oneForm_primitive hg ω)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
