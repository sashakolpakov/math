import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.MarkedUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedLevelAmbientParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionEquations

/-! # Prescribed Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PrescribedUniqueness.HilbertLevelPullback

noncomputable section

/-! The actual prescribed projective marks determine a point of the
full-level Hilbert pullback over its fixed configuration point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem projectiveSectionBaseChange_congr
    {S T : Scheme.{u}} {n : ℕ}
    {s t : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n}
    (h : s = t) (f : T ⟶ S) :
    Projective.SectionBaseChange.projectiveSectionBaseChange s f = Projective.SectionBaseChange.projectiveSectionBaseChange t f :=
  congrArg (fun a : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n =>
    Projective.SectionBaseChange.projectiveSectionBaseChange a f) h

private theorem projectiveSectionBaseChange_after_eq
    {X Y Z : Scheme.{u}} {n : ℕ}
    (s : Over.mk (𝟙 Z) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver Z n)
    (b q : Over.mk (𝟙 Y) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver Y n) (g : Y ⟶ Z) (f : X ⟶ Y)
    (hb : Projective.SectionBaseChange.projectiveSectionBaseChange s g = b)
    (hq : Projective.SectionBaseChange.projectiveSectionBaseChange b f = Projective.SectionBaseChange.projectiveSectionBaseChange q f) :
    Projective.SectionBaseChange.projectiveSectionBaseChange s (f ≫ g) = Projective.SectionBaseChange.projectiveSectionBaseChange q f :=
  (Projective.SectionBaseChange.projectiveSectionBaseChange_comp s g f).symm.trans
    ((projectiveSectionBaseChange_congr hb f).trans hq)

private theorem markedPoint_eq_baseChange
    (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N] {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (k : Multiplicative (Fin (2 * g) → ZMod N)) :
    MarkedUniqueness.HilbertLevelPullback.markedPoint S n P g Pm Pi N y k =
      Projective.SectionBaseChange.projectiveSectionBaseChange
        (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint
          (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
          (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N)
          (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N)
          (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N) k)
        y.left := by
  apply Over.OverMorphism.ext
  exact (congrArg (fun q : Over.mk (𝟙 T.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n => q.left)
    (Projective.SectionEquations.fullLevelMarkedProjectivePoint_baseChange
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N)
      (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N)
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N)
      y.left k)).symm

private theorem prescribedMarkedPoint_baseChange
    {S T : Scheme.{u}} (Z : Over S) {g N m : ℕ}
    (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel N) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (q : Fin m → (Over.mk (𝟙 Z.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension))
    (f : T ⟶ Z.left) (ha : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt Z A level P labels q f) (k : Fin m) :
    Projective.SectionBaseChange.projectiveSectionBaseChange (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P (labels k)) f =
      Projective.SectionBaseChange.projectiveSectionBaseChange (q k) f :=
  Projective.SectionEquations.projectiveSections_baseChange_eq_of_pullback_eq f _ _ (ha k)

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (Z : Over S) (c : Z ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)
    {m : ℕ} (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (q : Fin m → (Over.mk (𝟙 (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c).left) ⟶
      Projective.ProjectivePresentations.projectiveSpaceOver (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c).left n))

private theorem parameterMarkedPoint_eq (v : Multiplicative (Fin (2 * g) → ZMod N)) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
      (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
      (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) v =
    MarkedUniqueness.HilbertLevelPullback.markedPoint S n P g Pm Pi N (PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c) v := by
  apply Over.OverMorphism.ext
  rfl

private theorem parameterMarkedPoint_baseChange (v : Multiplicative (Fin (2 * g) → ZMod N)) :
    Projective.SectionBaseChange.projectiveSectionBaseChange
      (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N)
        (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N)
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N) v)
      (PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c).left =
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
      (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
      (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) v :=
  (markedPoint_eq_baseChange S n P g Pm Pi N (PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c) v).symm.trans
    (parameterMarkedPoint_eq S n P g Pm Pi N Z c v).symm

theorem parameterMarkedPoint_pullback {T : Over S}
    (a : T ⟶ PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
    (v : Multiplicative (Fin (2 * g) → ZMod N)) :
    Projective.SectionBaseChange.projectiveSectionBaseChange
      (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
        (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
        (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) v) a.left =
      MarkedUniqueness.HilbertLevelPullback.markedPoint S n P g Pm Pi N (a ≫ PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c) v := by
  let s : Over.mk (𝟙 (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left) ⟶
      Projective.ProjectivePresentations.projectiveSpaceOver (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left n :=
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N)
      (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N)
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N) v
  let b : Over.mk (𝟙 (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c).left) ⟶
      Projective.ProjectivePresentations.projectiveSpaceOver (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c).left n :=
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
      (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
      (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) v
  exact (projectiveSectionBaseChange_after_eq s b b
    (PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c).left a.left
    (parameterMarkedPoint_baseChange S n P g Pm Pi N Z c v) rfl).symm.trans
      (markedPoint_eq_baseChange S n P g Pm Pi N
        (a ≫ PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c) v).symm

theorem markedPoint_of_prescribed {T : Over S}
    (a : T ⟶ PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
    (ha : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
      (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
      (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) labels q a.left) (k : Fin m) :
    MarkedUniqueness.HilbertLevelPullback.markedPoint S n P g Pm Pi N (a ≫ PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c) (labels k) =
      Projective.SectionBaseChange.projectiveSectionBaseChange (q k) a.left := by
  let H := FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N
  let A := FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N
  let l := FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N
  let Q := FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N
  let s : Over.mk (𝟙 H.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver H.left n :=
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint H A l Q (labels k)
  let b : Over.mk (𝟙 (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c).left) ⟶
      Projective.ProjectivePresentations.projectiveSpaceOver (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c).left n :=
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
    (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
    (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) (labels k)
  have hb : Projective.SectionBaseChange.projectiveSectionBaseChange s (PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c).left = b :=
    parameterMarkedPoint_baseChange S n P g Pm Pi N Z c (labels k)
  have hm : Projective.SectionBaseChange.projectiveSectionBaseChange b a.left = Projective.SectionBaseChange.projectiveSectionBaseChange (q k) a.left :=
    prescribedMarkedPoint_baseChange (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
      (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
      (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) labels q a.left ha k
  exact (markedPoint_eq_baseChange S n P g Pm Pi N
    (a ≫ PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c) (labels k)).trans
      (projectiveSectionBaseChange_after_eq s b (q k)
        (PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c).left a.left hb hm)

theorem points_eq_of_chart_eq_of_prescribed {T : Over S} [IsLocallyNoetherian T.left]
    (a b : T ⟶ PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
    (ha : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
      (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
      (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) labels q a.left)
    (hb : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (PullbackParameter.HilbertLevelPullback.parameter S n P g Pm Pi N Z c)
      (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n P g Pm Pi N Z c).level
      (PullbackParameter.HilbertLevelPullback.projective S n P g Pm Pi N Z c) labels q b.left)
    (hZ : a ≫ PullbackParameter.HilbertLevelPullback.toChart S n P g Pm Pi N Z c = b ≫ PullbackParameter.HilbertLevelPullback.toChart S n P g Pm Pi N Z c)
    (hq : ∀ k, Projective.SectionBaseChange.projectiveSectionBaseChange (q k) a.left = Projective.SectionBaseChange.projectiveSectionBaseChange (q k) b.left) :
    a = b := by
  let aH := a ≫ PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c
  let bH := b ≫ PullbackParameter.HilbertLevelPullback.toFullLevel S n P g Pm Pi N Z c
  have haH : (a ≫ PullbackParameter.HilbertLevelPullback.toChart S n P g Pm Pi N Z c) ≫ c = aH ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N :=
    (PullbackParameter.HilbertLevelPullback.points S n P g Pm Pi N Z c T a).property
  have hbH : (b ≫ PullbackParameter.HilbertLevelPullback.toChart S n P g Pm Pi N Z c) ≫ c = bH ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N :=
    (PullbackParameter.HilbertLevelPullback.points S n P g Pm Pi N Z c T b).property
  have hH : aH ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N = bH ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N :=
    haH.symm.trans ((congrArg (fun z => z ≫ c) hZ).trans hbH)
  have hmarks (v : Multiplicative (Fin (2 * g) → ZMod N)) :
      MarkedUniqueness.HilbertLevelPullback.markedPoint S n P g Pm Pi N aH v = MarkedUniqueness.HilbertLevelPullback.markedPoint S n P g Pm Pi N bH v := by
    obtain ⟨k, rfl⟩ := labels.surjective v
    exact (markedPoint_of_prescribed S n P g Pm Pi N Z c labels q a ha k).trans
      ((hq k).trans (markedPoint_of_prescribed S n P g Pm Pi N Z c labels q b hb k).symm)
  have hab : aH = bH := MarkedUniqueness.HilbertLevelPullback.points_eq_of_hilbert_eq_markedPoints S n P g Pm Pi N aH bH hH hmarks
  apply (PullbackParameter.HilbertLevelPullback.points S n P g Pm Pi N Z c T).injective
  exact Subtype.ext (Prod.ext hZ hab)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PrescribedUniqueness.HilbertLevelPullback
