import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PrescribedCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicTransport

/-! # Prescribed Point Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedPointCriterion

noncomputable section

/-! The marked full-level stable parameter is described by its original
Hilbert point and the actual ordered projective configuration points.
This is the native point criterion used in overlap transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem sectionBaseChange_section_congr
    {S T : Scheme.{u}} {n : ℕ}
    {s t : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n} (h : s = t) (f : T ⟶ S) :
    Projective.SectionBaseChange.projectiveSectionBaseChange s f = Projective.SectionBaseChange.projectiveSectionBaseChange t f :=
  congrArg (fun q : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n =>
    Projective.SectionBaseChange.projectiveSectionBaseChange q f) h

private theorem sectionBaseChange_map_congr
    {S T : Scheme.{u}} {n : ℕ}
    (s : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) {f g : T ⟶ S} (h : f = g) :
    Projective.SectionBaseChange.projectiveSectionBaseChange s f = Projective.SectionBaseChange.projectiveSectionBaseChange s g :=
  congrArg (fun q : T ⟶ S => Projective.SectionBaseChange.projectiveSectionBaseChange s q) h

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (H : Polynomial ℚ)

def stableHilbertPrescribedPoint {T : Over (Spec (.of R))}
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (z : Fin m) :
    Over.mk (𝟙 T.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n :=
  Projective.SectionBaseChange.projectiveSectionBaseChange
    (Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate j.exponent
      j.complement j.balanced j.complete z)
    (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H).left

namespace StableHilbertFullLevel
variable (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]

theorem markedPoint_baseChange_chartPoint {T : Over (Spec (.of R))}
    (a : T ⟶ LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N) (z : Fin m) :
    Projective.SectionBaseChange.projectiveSectionBaseChange (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N z) a.left =
      stableHilbertPrescribedPoint R i j D H (a ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N) z := by
  change @Eq (Over.mk (𝟙 T.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n)
    (Projective.SectionBaseChange.projectiveSectionBaseChange (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N z) a.left)
    (stableHilbertPrescribedPoint R i j D H (a ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N) z)
  let s := Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete z
  have hm : @Eq
      (Over.mk (𝟙 (LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N).left) ⟶
        Projective.ProjectivePresentations.projectiveSpaceOver (LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N).left n)
      (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N z)
      (Projective.SectionBaseChange.projectiveSectionBaseChange s (LevelParameter.StableHilbertLevel.toCoefficientChart R i j D H hH g Hm Hi N).left) :=
    MarkedPointNaturality.StableHilbertLevel.markedPoint_eq_baseChange R i j D H hH g Hm Hi N z
  have hc : a.left ≫ (LevelParameter.StableHilbertLevel.toCoefficientChart R i j D H hH g Hm Hi N).left =
      ((a ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N) ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H).left := by
    change a.left ≫ ((LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N).left ≫
        (IntrinsicTransport.stableHilbertChartAmbientMap R i j D H).left) =
      (a.left ≫ (LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N).left) ≫
        (IntrinsicTransport.stableHilbertChartAmbientMap R i j D H).left
    exact (Category.assoc _ _ _).symm
  exact (sectionBaseChange_section_congr (n := n) hm a.left).trans
    ((Projective.SectionBaseChange.projectiveSectionBaseChange_comp s
      (LevelParameter.StableHilbertLevel.toCoefficientChart R i j D H hH g Hm Hi N).left a.left).trans
        (sectionBaseChange_map_congr s hc))

variable (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

theorem hasPoint_iff_hilbert_markedPoints {T : Over (Spec (.of R))}
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) :
    (∃ u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels = c) ↔
    ∃ y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (.of R)) n H g Hm Hi N,
      y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
        c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH ∧
      ∀ z, HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint (Spec (.of R)) n H g Hm Hi N y (labels z) =
        stableHilbertPrescribedPoint R i j D H c z := by
  let Z := Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H
  let q := ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH
  let B := LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N
  let h := HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (.of R)) n H g Hm Hi N Z q
  constructor
  · rintro ⟨u, hu⟩
    let a := u ≫ LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels
    have ha : a ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N = c :=
      (Category.assoc _ _ _).trans hu
    have hap : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt B (LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N).abelian
        (LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N).level (LevelParameter.StableHilbertLevel.basePresentation R i j D H hH g Hm Hi N)
        labels (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N) a.left :=
      (LevelParameter.StableHilbertLevel.pointEquiv R i j D H hH g Hm Hi N labels T u).property
    refine ⟨a ≫ h, ?_, fun z => ?_⟩
    · exact (HilbertLevel.PullbackParameter.HilbertLevelPullback.points (Spec (.of R)) n H g Hm Hi N Z q T a).property.symm.trans
        (congrArg (fun a => a ≫ q) ha)
    · exact (HilbertLevel.PrescribedUniqueness.HilbertLevelPullback.markedPoint_of_prescribed (Spec (.of R)) n H g Hm Hi N
        Z q labels (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N) a hap z).trans
        ((markedPoint_baseChange_chartPoint R i j D H hH g Hm Hi N a z).trans
          (congrArg (fun a => stableHilbertPrescribedPoint R i j D H a z) ha))
  · rintro ⟨y, hy, hm⟩
    let a : T ⟶ B := pullback.lift c y hy.symm
    have ha : a ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N = c := pullback.lift_fst _ _ _
    have hh : a ≫ h = y := pullback.lift_snd _ _ _
    have hap : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt B (LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N).abelian
        (LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N).level (LevelParameter.StableHilbertLevel.basePresentation R i j D H hH g Hm Hi N)
        labels (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N) a.left := by
      apply (HilbertLevel.PrescribedCriterion.HilbertFullLevelPullback.prescribed_iff_markedPoint (Spec (.of R)) n H g Hm Hi N
        Z q labels (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N) a).mpr
      intro z
      have hx := markedPoint_baseChange_chartPoint R i j D H hH g Hm Hi N a z
      exact (congrArg (fun b => HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint (Spec (.of R)) n H g Hm Hi N
        b (labels z)) hh).trans ((hm z).trans
          ((congrArg (fun b => stableHilbertPrescribedPoint R i j D H b z) ha).symm.trans hx.symm))
    let u := (LevelParameter.StableHilbertLevel.pointEquiv R i j D H hH g Hm Hi N labels T).symm ⟨a, hap⟩
    have hu : u ≫ LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels = a :=
      congrArg Subtype.val ((LevelParameter.StableHilbertLevel.pointEquiv R i j D H hH g Hm Hi N labels T).apply_symm_apply ⟨a, hap⟩)
    refine ⟨u, ?_⟩
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun b => b ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N) hu).trans ha)

end StableHilbertFullLevel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedPointCriterion
