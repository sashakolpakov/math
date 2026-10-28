import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeEndDescent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseTraceConvolution

/-! # Hecke End Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The descended integral Hecke endomorphism has the actual trace
formula on component differences, over every test scheme over K. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
theorem HeckeEndPoints.fieldSpectraPullback_faithful {k L : Type u} [Field k] [Field L]
    (p : Spec (.of L) ⟶ Spec (.of k)) : (Over.pullback p).Faithful := by
  have : Flat p := by
    obtain ⟨r, rfl⟩ := Spec.map_surjective p
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField k) r.hom
  have : Surjective p := ⟨Function.surjective_to_subsingleton _⟩
  have : QuasiCompact p := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  infer_instance

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.HeckeEndPoints_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.HeckeEndPoints_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm
local instance Data.SphericalPELAlbaneseData.HeckeEndPoints_local3 : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.HeckeEndPoints_local4 : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

theorem Data.SphericalPELAlbaneseData.heckeEnd_schemeMap_baseChange (t : Local.IntegralType s) :
    (Over.pullback D.complexGenericPoint).map (End.endSchemeMap D.albaneseGroup.X (D.heckeEnd hg t)) =
      End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t) := by
  rw [← BaseChange.endBaseChange_schemeMap, D.heckeEnd_baseChange hg]

theorem Data.SphericalPELAlbaneseData.heckeEnd_differences (t : Local.IntegralType s) (j : Fin D.componentCount)
    {T : Over (Spec (.of K))} (x y : T ⟶ D.componentGeneric j) :
    ((x ≫ D.componentInclusion j ≫ D.albaneseMap hg) /
      (y ≫ D.componentInclusion j ≫ D.albaneseMap hg)) ≫
        End.endSchemeMap D.albaneseGroup.X (D.heckeEnd hg t) =
      (x ≫ D.componentInclusion j ≫ D.albaneseTrace hg t) /
        (y ≫ D.componentInclusion j ≫ D.albaneseTrace hg t) := by
  have : (Over.pullback D.complexGenericPoint).Faithful :=
    HeckeEndPoints.fieldSpectraPullback_faithful D.complexGenericPoint
  apply (Over.pullback D.complexGenericPoint).map_injective
  simp only [Functor.map_comp, div_eq_mul_inv, Functor.map_mul, Functor.map_inv',
    D.heckeEnd_schemeMap_baseChange hg]
  simpa only [Functor.map_comp, div_eq_mul_inv] using D.complexHeckeEnd_baseChange_differences hg t j
    ((Over.pullback D.complexGenericPoint).map x) ((Over.pullback D.complexGenericPoint).map y)

theorem Data.SphericalPELAlbaneseData.heckeEnd_point_push (t : Local.IntegralType s)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (j : Fin D.componentCount) (x y : Over.mk b ⟶ D.componentGeneric j) :
    D.endPoint (D.heckeEnd hg t) (D.aPoint hg j x - D.aPoint hg j y) =
      ((D.neighbors t b (x ≫ D.componentInclusion j)).map (D.aTotalPoint hg)).sum -
        ((D.neighbors t b (y ≫ D.componentInclusion j)).map (D.aTotalPoint hg)).sum := by
  rw [← D.albaneseTrace_point_sum hg, ← D.albaneseTrace_point_sum hg]
  change Additive.ofMul ((((x ≫ D.componentInclusion j) ≫ D.albaneseMap hg) /
    ((y ≫ D.componentInclusion j) ≫ D.albaneseMap hg)) ≫
      End.endSchemeMap D.albaneseGroup.X (D.heckeEnd hg t)) =
    Additive.ofMul (((x ≫ D.componentInclusion j) ≫ D.albaneseTrace hg t) /
      ((y ≫ D.componentInclusion j) ≫ D.albaneseTrace hg t))
  simpa only [Category.assoc] using congrArg Additive.ofMul (D.heckeEnd_differences hg t j x y)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
