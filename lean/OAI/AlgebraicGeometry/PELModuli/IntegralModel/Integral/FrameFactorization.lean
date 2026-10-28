import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.CanonicalFrame
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization

/-! # Frame Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization.IntegralLevelCover

noncomputable section

section

/-! Full-level construction over arbitrary bases where the level is invertible.
Adapted from the corresponding proved ReferenceFamily construction; no characteristic-zero
hypothesis or supplied torsion trivialization is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover

variable {S : Scheme.{0}} {g N : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (hN : ∀ x : S, IsUnit (N : S.presheaf.stalk x))

theorem relativeLevel_frame_range [NeZero N] (T : Over S)
    (f : T ⟶ AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (β : (A.pullback T.hom).FullLevel N) :
    Set.range f.left ⊆ (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N) : Set (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).left) := by
  let : IsIso ((Over.pullback f.left).map (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _))) :=
    AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover.universalFrame_pullback_isIso_of_relative_split A T f β
  rintro s ⟨t, rfl⟩
  apply (FrameLocus.IntegralLevelCover.mem_fullFrameOpen_iff A hN _).mpr
  intro y hy
  exact AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover.overPullbackMap_spans_of_isIso
    (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)) f.left y ⟨t, hy.symm⟩

/-- The classifying frame map of a relative full level factors through
the actual full-frame open subscheme. -/
def fullFrameOfRelativeLevel [NeZero N] (T : Over S)
    (β : (A.pullback T.hom).FullLevel N) : T ⟶ FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N) := by
  let f := AbelianModuli.ReferenceFamily.IndependentFrames.LevelCover.frameOfRelativeLevel A T β
  have hr : Set.range f.left ⊆ Set.range (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N)).ι := by
    rw [Scheme.Opens.range_ι]
    exact relativeLevel_frame_range A hN T f β
  let l := IsOpenImmersion.lift (FrameLocus.IntegralLevelCover.fullFrameOpen A hN).ι f.left hr
  have hl : l ≫ (FrameLocus.IntegralLevelCover.fullFrameOpen A hN).ι = f.left := IsOpenImmersion.lift_fac _ _ hr
  refine Over.homMk l ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom) hl).trans f.w)

theorem fullFrameOfRelativeLevel_inclusion [NeZero N] (T : Over S)
    (β : (A.pullback T.hom).FullLevel N) :
    fullFrameOfRelativeLevel A hN T β ≫ CanonicalFrame.IntegralLevelCover.fullFrameInclusion A hN = AbelianModuli.ReferenceFamily.IndependentFrames.LevelCover.frameOfRelativeLevel A T β := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N)).ι
    (AbelianModuli.ReferenceFamily.IndependentFrames.LevelCover.frameOfRelativeLevel A T β).left _

end

/-! Full-level construction over arbitrary bases where the level is invertible.
Adapted from the corresponding proved ReferenceFamily construction; no characteristic-zero
hypothesis or supplied torsion trivialization is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover

variable {S : Scheme.{0}} {g N : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (hN : ∀ x : S, IsUnit (N : S.presheaf.stalk x))

variable [NeZero N]

instance fullFrameInclusion_mono : Mono (CanonicalFrame.IntegralLevelCover.fullFrameInclusion A hN (N := N)) := by
  let : Mono (CanonicalFrame.IntegralLevelCover.fullFrameInclusion A hN (N := N)).left :=
    inferInstanceAs (Mono (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N)).ι)
  exact Over.mono_of_mono_left _

/-- The constructed full-frame scheme classifies full levels on every
test scheme, with its canonical universal coefficient map. -/
def fullFramePointsEquiv (T : Over S) :
    (T ⟶ FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N)) ≃ (A.pullback T.hom).FullLevel N where
  toFun f := (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel A hN).restrict f
  invFun β := fullFrameOfRelativeLevel A hN T β
  left_inv f := by
    apply (cancel_mono (CanonicalFrame.IntegralLevelCover.fullFrameInclusion A hN)).mp
    exact (fullFrameOfRelativeLevel_inclusion A hN T _).trans
      ((AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover.frameOfRelativeLevel_restrict A f _).trans
        (congrArg (fun q => f ≫ q) (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel_classifying A hN)))
  right_inv β := by
    apply AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover.frameOfRelativeLevel_injective A T
    exact (AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover.frameOfRelativeLevel_restrict A (fullFrameOfRelativeLevel A hN T β) _).trans
      ((congrArg (fun q => fullFrameOfRelativeLevel A hN T β ≫ q)
        (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel_classifying A hN)).trans
          (fullFrameOfRelativeLevel_inclusion A hN T β))

theorem fullFramePointsEquiv_classifying (T : Over S)
    (f : T ⟶ FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N)) :
    AbelianModuli.ReferenceFamily.IndependentFrames.LevelCover.frameOfRelativeLevel A T (fullFramePointsEquiv A hN T f) = f ≫ CanonicalFrame.IntegralLevelCover.fullFrameInclusion A hN :=
  (AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover.frameOfRelativeLevel_restrict A f _).trans
    (congrArg (fun q => f ≫ q) (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel_classifying A hN))

/-- The classification commutes with the actual pullback and transport
maps of the full-level family functor. -/
theorem fullFramePointsEquiv_natural {T U : Over S} (j : T ⟶ U)
    (f : U ⟶ FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N)) :
    fullFramePointsEquiv A hN T (j ≫ f) = (fullFramePointsEquiv A hN U f).restrict j := by
  apply AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover.frameOfRelativeLevel_injective A T
  exact (fullFramePointsEquiv_classifying A hN T (j ≫ f)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => j ≫ q) (fullFramePointsEquiv_classifying A hN U f).symm).trans
        (AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover.frameOfRelativeLevel_restrict A j _).symm))

def fullLevelRepresentable :
    (AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover.fullLevelFamilyFunctor A (N := N)).RepresentableBy (FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N)) where
  homEquiv {T} := fullFramePointsEquiv A hN T
  homEquiv_comp j f := fullFramePointsEquiv_natural A hN j f

include hN in
/-- Every abelian scheme with invertible level has an actual finite
etale parameter scheme for all full levels at each nonzero level. -/
theorem finite_etale_fullLevel_parameter :
    ∃ F : Over S, IsFinite F.hom ∧ Etale F.hom ∧
      Nonempty ((AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover.fullLevelFamilyFunctor A (N := N)).RepresentableBy F) :=
  ⟨FrameLocus.IntegralLevelCover.fullFrameScheme A hN, (FrameLocus.IntegralLevelCover.fullFrameScheme_finite_etale A hN).1,
    (FrameLocus.IntegralLevelCover.fullFrameScheme_finite_etale A hN).2, ⟨fullLevelRepresentable A hN⟩⟩

theorem fullLevel_unique_fullFrame_classifying (T : Over S)
    (β : (A.pullback T.hom).FullLevel N) :
    ∃! f : T ⟶ FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N),
      (CanonicalFrame.IntegralLevelCover.canonicalFullFrameLevel A hN).restrict f = β := by
  refine ⟨(fullFramePointsEquiv A hN T).symm β, (fullFramePointsEquiv A hN T).apply_symm_apply β, ?_⟩
  intro f hf
  exact (fullFramePointsEquiv A hN T).injective
    (hf.trans ((fullFramePointsEquiv A hN T).apply_symm_apply β).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameFactorization.IntegralLevelCover
