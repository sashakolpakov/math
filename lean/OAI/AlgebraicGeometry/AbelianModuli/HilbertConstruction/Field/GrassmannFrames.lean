import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PairChartCover
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Grassmann Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GrassmannFrames

noncomputable section

/-! A pair of Grassmannian maps over a field admits simultaneous global normalized charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {S : Scheme.{u}} (K : Type u) [Field K] (f : Spec (CommRingCat.of K) ⟶ S)
variable (q : Over.mk f ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : Over.mk f ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)

theorem fieldGrassmannPair_global_charts :
    ∃ (a : ι → ν) (b : κ → μ) (v : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S)
      (w : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S),
      v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = q ∧ w ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = k := by
  let D := Grassmann.PairChartCover.grassmannPairChartCover q k
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  obtain ⟨i, y, hy⟩ := D.cover.exists_eq p
  have : Surjective (D.cover.f i) := ⟨fun x => ⟨y, hy.trans (Subsingleton.elim (α := PrimeSpectrum K) p x)⟩⟩
  have : IsIso (D.cover.f i) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  let c := Embedded.FamilyOpenCover.overOpenCoverMap (Over.mk f) D.cover i
  have : IsIso ((Over.forget S).map c) := inferInstanceAs (IsIso (D.cover.f i))
  have : IsIso c := isIso_of_reflects_iso c (Over.forget S)
  refine ⟨D.sourceColumns i, D.targetColumns i, inv c ≫ D.sourceLift i, inv c ≫ D.targetLift i, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => inv c ≫ g) (D.source_fac i)).trans (IsIso.inv_hom_id_assoc c q))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => inv c ≫ g) (D.target_fac i)).trans (IsIso.inv_hom_id_assoc c k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GrassmannFrames
