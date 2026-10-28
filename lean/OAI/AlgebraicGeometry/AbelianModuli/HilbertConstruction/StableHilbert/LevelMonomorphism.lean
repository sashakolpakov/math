import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.MarkedPointNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PrescribedUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TestMonomorphism

/-! # Level Monomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel

noncomputable section

/-! The original stable Hilbert point determines its full-level family
once all prescribed torsion marks are imposed. Testing the native
self-fiber product extends this uniqueness to every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (P : Polynomial ℚ)
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

def toHilbertChart : LevelParameter.StableHilbertLevel.parameter R i j D P hP g Pm Pi N labels ⟶
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P :=
  LevelParameter.StableHilbertLevel.inclusion R i j D P hP g Pm Pi N labels ≫ LevelParameter.StableHilbertLevel.toChart R i j D P hP g Pm Pi N

instance parameter_noetherian : IsNoetherian (LevelParameter.StableHilbertLevel.parameter R i j D P hP g Pm Pi N labels).left :=
  (LevelParameter.StableHilbertLevel.quasiProjective R i j D P hP g Pm Pi N labels).noetherian

instance toHilbertChart_locallyOfFiniteType :
    LocallyOfFiniteType (toHilbertChart R i j D P hP g Pm Pi N labels).left := by
  let f := toHilbertChart R i j D P hP g Pm Pi N labels
  let : LocallyOfFiniteType (f.left ≫ (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).hom) :=
    f.w.symm ▸ (LevelParameter.StableHilbertLevel.quasiProjective R i j D P hP g Pm Pi N labels).locallyFiniteType
  exact locallyOfFiniteType_of_comp f.left (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).hom

theorem points_eq_of_toHilbertChart_eq
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a b : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D P hP g Pm Pi N labels)
    (h : a ≫ toHilbertChart R i j D P hP g Pm Pi N labels =
      b ≫ toHilbertChart R i j D P hP g Pm Pi N labels) : a = b := by
  let inc := LevelParameter.StableHilbertLevel.inclusion R i j D P hP g Pm Pi N labels
  let aa := a ≫ inc
  let bb := b ≫ inc
  have hZ : aa ≫ LevelParameter.StableHilbertLevel.toChart R i j D P hP g Pm Pi N = bb ≫ LevelParameter.StableHilbertLevel.toChart R i j D P hP g Pm Pi N :=
    (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  have ha : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (LevelParameter.StableHilbertLevel.base R i j D P hP g Pm Pi N)
      (LevelParameter.StableHilbertLevel.baseFamily R i j D P hP g Pm Pi N).abelian (LevelParameter.StableHilbertLevel.baseFamily R i j D P hP g Pm Pi N).level
      (LevelParameter.StableHilbertLevel.basePresentation R i j D P hP g Pm Pi N) labels
      (LevelParameter.StableHilbertLevel.markedPoint R i j D P hP g Pm Pi N) aa.left :=
    (LevelParameter.StableHilbertLevel.pointEquiv R i j D P hP g Pm Pi N labels T a).property
  have hb : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (LevelParameter.StableHilbertLevel.base R i j D P hP g Pm Pi N)
      (LevelParameter.StableHilbertLevel.baseFamily R i j D P hP g Pm Pi N).abelian (LevelParameter.StableHilbertLevel.baseFamily R i j D P hP g Pm Pi N).level
      (LevelParameter.StableHilbertLevel.basePresentation R i j D P hP g Pm Pi N) labels
      (LevelParameter.StableHilbertLevel.markedPoint R i j D P hP g Pm Pi N) bb.left :=
    (LevelParameter.StableHilbertLevel.pointEquiv R i j D P hP g Pm Pi N labels T b).property
  have hab : aa = bb :=
    HilbertLevel.PrescribedUniqueness.HilbertLevelPullback.points_eq_of_chart_eq_of_prescribed (Spec (.of R)) n P g Pm Pi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) (ClassifyingMap.stableConfigurationHilbertClassifier R i j D P hP)
      labels (LevelParameter.StableHilbertLevel.markedPoint R i j D P hP g Pm Pi N) aa bb ha hb hZ
      (MarkedPointNaturality.StableHilbertLevel.markedPoint_baseChange_eq_of_toChart_eq R i j D P hP g Pm Pi N aa bb hZ)
  let : Mono inc := Over.mono_of_mono_left inc
  exact (cancel_mono inc).mp hab

instance toHilbertChart_mono : Mono (toHilbertChart R i j D P hP g Pm Pi N labels) :=
  Noetherian.TestMonomorphism.over_mono_of_locallyNoetherian_tests (toHilbertChart R i j D P hP g Pm Pi N labels)
    (fun _ _ a b h => points_eq_of_toHilbertChart_eq R i j D P hP g Pm Pi N labels a b h)

instance toHilbertChart_left_mono : Mono (toHilbertChart R i j D P hP g Pm Pi N labels).left :=
  Over.mono_left_of_mono _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel
