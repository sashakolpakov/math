import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexAlbaneseCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseTrace

/-! # Complex Albanese End -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Componentwise Albanese factorizations assemble into an actual
integral algebraic endomorphism of the complete complex Albanese. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem ComplexAlbaneseEnd.endSchemeMap_sum {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    {I : Type*} (s : Finset I) (f : I → End.IntegralEnd A) :
    End.endSchemeMap A (∑ i ∈ s, f i) = ∏ i ∈ s, End.endSchemeMap A (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, BaseChange.endSchemeMap_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, BaseChange.endSchemeMap_add, ih]

theorem ComplexAlbaneseEnd.comp_endSchemeMap_sum {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    {I : Type*} (s : Finset I) (f : I → End.IntegralEnd A) {T : Over S} (z : T ⟶ A) :
    z ≫ End.endSchemeMap A (∑ i ∈ s, f i) = ∏ i ∈ s, z ≫ End.endSchemeMap A (f i) := by
  rw [ComplexAlbaneseEnd.endSchemeMap_sum]
  let F : (A ⟶ A) →* (T ⟶ A) := ((yonedaGrpObj A).map z.op).hom
  exact map_prod F _ _

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.ComplexAlbaneseEnd_local1 : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.ComplexAlbaneseEnd_local2 : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

def Data.SphericalPELAlbaneseData.complexProductEnd
    (f : ∀ j, D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X) :
    End.IntegralEnd D.complexAlbanese.X :=
  ∑ j : Fin D.componentCount, End.endOfSchemeMap D.complexAlbanese.X
    (D.complexAlbaneseProjection j ≫ D.complexComponentFactor hg j (f j))

theorem Data.SphericalPELAlbaneseData.complexProductEnd_component
    (f : ∀ j, D.components.complexSurface D.complexPoint j ⟶ D.complexAlbanese.X)
    (j : Fin D.componentCount) :
    D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg ≫
      End.endSchemeMap D.complexAlbanese.X (D.complexProductEnd hg f) =
        D.normalizedComplexComponentMap j (f j) := by
  classical
  rw [Data.SphericalPELAlbaneseData.complexProductEnd, ← Category.assoc, ComplexAlbaneseEnd.comp_endSchemeMap_sum]
  have he (k : Fin D.componentCount) :
      (D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg) ≫
        End.endSchemeMap D.complexAlbanese.X
          (End.endOfSchemeMap D.complexAlbanese.X
            (D.complexAlbaneseProjection k ≫ D.complexComponentFactor hg k (f k))) =
      (D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg ≫ D.complexAlbaneseProjection k) ≫
        D.complexComponentFactor hg k (f k) := by
    rw [End.endSchemeMap_ofSchemeMap]
    simp only [Category.assoc]
  simp only [he]
  rw [Finset.prod_eq_single j]
  · rw [D.complexAlbanese_component_self hg, D.complexComponentFactor_equation hg]
  · intro k _ hkj
    rw [D.complexAlbanese_component_ne hg j k (Ne.symm hkj), MonObj.one_comp]
  · simp

def Data.SphericalPELAlbaneseData.complexHeckeEnd (t : Local.IntegralType s) : End.IntegralEnd D.complexAlbanese.X :=
  D.complexProductEnd hg (fun j => D.complexSourceInclusion j ≫
    (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t))

theorem Data.SphericalPELAlbaneseData.complexHeckeEnd_component (t : Local.IntegralType s) (j : Fin D.componentCount) :
    D.complexSourceInclusion j ≫ D.complexAlbaneseMap hg ≫
      End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t) =
        D.normalizedComplexComponentMap j (D.complexSourceInclusion j ≫
          (Over.pullback D.complexGenericPoint).map (D.albaneseTrace hg t)) :=
  D.complexProductEnd_component hg _ j

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
