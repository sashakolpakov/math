import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingPowerSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.PowerTensorRelation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackSectionBound

/-! # Difference Section Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On any integral closed subscheme of an abelian variety, sections of a polarized automorphism difference's pulled-back embedding bundle have a fixed finite-dimensional bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
variable {Y : Scheme.{u}} [IsIntegral Y] (i : Y ⟶ A.abelian.scheme.left)
variable [IsClosedImmersion i] [Flat (i ≫ A.abelian.scheme.hom)]
variable [LocallyOfFinitePresentation (i ≫ A.abelian.scheme.hom)]

theorem Moduli.Isomorphisms.LevelPreservingIso.differenceSections_finite_and_bound (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ A.abelian.scheme.hom)).obj
      (E.power.pullback (i ≫ (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left)).sheaf) ∧
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ A.abelian.scheme.hom)).obj
      (E.power.pullback (i ≫ (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left)).sheaf) ≤
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ A.abelian.scheme.hom)).obj
      ((E.power.pullback i).tensorPower 4).sheaf) := by
  let a := (e.abelian.hom * (𝟙 A.abelian.scheme)).left
  let b := (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left
  let L := E.power.pullback (i ≫ a)
  let M := E.power.pullback (i ≫ b)
  let B := (E.power.pullback i).tensorPower 4
  let h : (L.tensor M).sheaf ≅ B.sheaf :=
    E.power.pullbackTensorRelationIso a b 4 (e.embeddingPower_sum_difference_iso A E) i
  have : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (i ≫ A.abelian.scheme.hom)).obj B.sheaf) :=
    E.closedPullbackPowerSections_finite A.abelian.scheme.hom i 4
  obtain ⟨j, hj⟩ := Generated.PullbackSectionBound.generatingSections_pullback_nonempty (i ≫ a) E.power E.sections E.covers
  let s : Line.Bundles.structureModule Y ⟶ L.sheaf := Ample.LineBundles.pullbackSection (i ≫ a) (E.sections j)
  have : Nonempty (Ample.LineBundles.sectionNonvanishing s) := hj
  exact ⟨Generated.PullbackSectionBound.tensorFactorSections_finite (i ≫ A.abelian.scheme.hom) L M B s h,
    Generated.PullbackSectionBound.tensorFactorSections_finrank_le (i ≫ A.abelian.scheme.hom) L M B s h⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
