import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Flat.Localization

/-! # Point Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian

noncomputable section

/-! The quotient recovered from an affine Grassmannian point is finite projective of the required rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {R : CommRingCat.{u}}
variable {g : Over.mk (𝟙 (Spec R)) ⟶ Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R)}
variable (D : PointFiniteCharts.FiniteGrassmannianMatrixPresentation R g)

def PointFiniteCharts.FiniteGrassmannianMatrixPresentation.quotientLocalizedEquiv (i : D.index) :
    LocalizedModule.Away (D.denominator i) ((ν → R) ⧸ D.relations) ≃ₗ[Localization.Away (D.denominator i)]
      (ι → Localization.Away (D.denominator i)) :=
  LocalizedModule.equivTensorProduct (Submonoid.powers (D.denominator i)) ((ν → R) ⧸ D.relations) ≪≫ₗ
    (Coordinate.GrassmannianBaseChange.Grassmannian.coordinateBaseChangeQuotientEquiv (S := Localization.Away (D.denominator i)) D.relations).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (D.relations_localized i) ≪≫ₗ
        Normalized.Quotients.Grassmannian.normalizedQuotientEquiv (D.columns i) (D.matrix i) (D.normalized i)

theorem PointFiniteCharts.FiniteGrassmannianMatrixPresentation.quotient_finitePresentation :
    Module.FinitePresentation R ((ν → R) ⧸ D.relations) := by
  apply Module.FinitePresentation.of_localizationSpan (Set.range D.denominator) D.denominators_span
  rintro ⟨r, i, rfl⟩
  have : Module.Free (Localization.Away (D.denominator i))
      (LocalizedModule.Away (D.denominator i) ((ν → R) ⧸ D.relations)) :=
    Module.Free.of_equiv (D.quotientLocalizedEquiv i).symm
  exact Module.finitePresentation_of_projective _ _

theorem PointFiniteCharts.FiniteGrassmannianMatrixPresentation.quotient_flat :
    Module.Flat R ((ν → R) ⧸ D.relations) := by
  apply Module.flat_of_localized_span R ((ν → R) ⧸ D.relations)
    (Set.range D.denominator) D.denominators_span
  rintro ⟨r, i, rfl⟩
  have : Module.Free (Localization.Away (D.denominator i))
      (LocalizedModule.Away (D.denominator i) ((ν → R) ⧸ D.relations)) :=
    Module.Free.of_equiv (D.quotientLocalizedEquiv i).symm
  have : Module.Flat R (Localization.Away (D.denominator i)) :=
    IsLocalization.flat _ (Submonoid.powers (D.denominator i))
  exact Module.Flat.trans R (Localization.Away (D.denominator i)) _

theorem PointFiniteCharts.FiniteGrassmannianMatrixPresentation.quotient_projective :
    Module.Projective R ((ν → R) ⧸ D.relations) := by
  have := D.quotient_finitePresentation
  have := D.quotient_flat
  exact Module.Flat.projective_of_finitePresentation

theorem PointFiniteCharts.FiniteGrassmannianMatrixPresentation.quotient_rank (p : PrimeSpectrum R) :
    Module.rankAtStalk ((ν → R) ⧸ D.relations) p = Fintype.card ι := by
  have := D.quotient_flat
  obtain ⟨i, hi⟩ := D.covers p
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (D.denominator i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ (D.denominator i)]
    exact hi
  obtain ⟨q, hq⟩ := hp
  have : Nontrivial (Localization.Away (D.denominator i)) := q.nontrivial
  have hbase := Module.rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange (Submonoid.powers (D.denominator i)) ((ν → R) ⧸ D.relations)) q
  rw [hq] at hbase
  rw [← hbase, congrFun (Module.rankAtStalk_eq_of_equiv (D.quotientLocalizedEquiv i)) q,
    Module.rankAtStalk_eq_finrank_of_free]
  simp

def PointFiniteCharts.FiniteGrassmannianMatrixPresentation.quotient : Module.Grassmannian R (ν → R) (Fintype.card ι) where
  toSubmodule := D.relations
  finite_quotient := inferInstance
  projective_quotient := D.quotient_projective
  rankAtStalk_eq := D.quotient_rank

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian
