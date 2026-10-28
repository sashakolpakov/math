import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.Monomorphisms

/-! # Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover

noncomputable section

section

/-! Relative full levels factor through the constructed finite etale
full-frame locus. The proof detects the absence of omitted torsion
points after actual scheme base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {B B' : Scheme.{0}} {X Y : Over B}

theorem overPullbackMap_spans_of_isIso (m : X ⟶ Y) (u : B' ⟶ B)
    [IsIso ((Over.pullback u).map m)] :
    ∀ y : Y.left, Y.hom y ∈ Set.range u → y ∈ Set.range m.left := by
  let : IsIso ((Over.pullback u).map m).left :=
    inferInstanceAs (IsIso ((Over.forget B').map ((Over.pullback u).map m)))
  intro y hy
  have hy' : y ∈ Set.range (pullback.fst Y.hom u) := by
    rw [Scheme.Pullback.range_fst]
    exact hy
  obtain ⟨z, hz⟩ := hy'
  obtain ⟨w, hw⟩ := ((Over.pullback u).map m).left.surjective z
  refine ⟨pullback.fst X.hom u w, ?_⟩
  have hc := congrArg (fun q : pullback X.hom u ⟶ Y.left => q w)
    (SpanningBaseChange.LevelCover.overPullbackMap_isPullback m u).w
  change m.left (pullback.fst X.hom u w) = _
  exact hc.trans ((congrArg (pullback.fst Y.hom u) hw).trans hz)

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def relativeLevelOnFramePullback (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (β : (A.pullback T.hom).FullLevel N) :
    ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).pullback f.left).FullLevel N := by
  let e := A.pullbackCongrIso T.hom (f.left ≫ (Level.Cover.LevelCover.frameScheme A N).hom) f.w.symm
  let e' := A.pullbackCompIso (Level.Cover.LevelCover.frameScheme A N).hom f.left
  exact (β.transport e).transport e'

theorem universalFrame_pullback_isIso_of_relative_split [NeZero N]
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (β : (A.pullback T.hom).FullLevel N) :
    IsIso ((Over.pullback f.left).map (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _))) := by
  let m := GroupScheme.LevelCover.frameGroupSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)
  let F := Over.pullback f.left
  let q := F.mapGrp.map m
  let : Mono m.hom.hom := GroupScheme.LevelCover.frameSchemeMap_mono A _ _
  have hq : Mono q.hom.hom := inferInstanceAs (Mono (F.map m.hom.hom))
  let eX := Level.BaseChange.GroupBaseChange.constantBaseChangeYonedaIso (g := g) (N := N) f.left ≪≫
    HilbertConstruction.Geometric.GeometricLevel.constantFullLevelYonedaIso g N T.left
  let eY := Level.BaseChange.GroupBaseChange.torsionBaseChangeYonedaIso
    (A.pullback (Level.Cover.LevelCover.frameScheme A N).hom) f.left N ≪≫
      (((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).pullback f.left).torsionSchemeYonedaIso N) ≪≫
      (relativeLevelOnFramePullback A T f β).symm
  let : IsIso q := Finite.Monomorphisms.FiniteGroupIso.isIso_of_mono_constant_presentations q hq eX eY
  exact inferInstanceAs (IsIso ((Grp.forget (Over T.left)).map q))

variable {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

theorem relativeLevel_frame_range [NeZero N] (T : Over S)
    (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (β : (A.pullback T.hom).FullLevel N) :
    Set.range f.left ⊆ (Locus.LevelCover.fullFrameOpen A p (N := N) : Set (Level.Cover.LevelCover.frameScheme A N).left) := by
  let : IsIso ((Over.pullback f.left).map (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _))) :=
    universalFrame_pullback_isIso_of_relative_split A T f β
  rintro s ⟨t, rfl⟩
  apply (Locus.LevelCover.mem_fullFrameOpen_iff A p _).mpr
  intro y hy
  exact overPullbackMap_spans_of_isIso
    (GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)) f.left y ⟨t, hy.symm⟩

/-- The classifying frame map of a relative full level factors through
the actual full-frame open subscheme. -/
def fullFrameOfRelativeLevel [NeZero N] (T : Over S)
    (β : (A.pullback T.hom).FullLevel N) : T ⟶ Locus.LevelCover.fullFrameScheme A p (N := N) := by
  let f := IndependentFrames.LevelCover.frameOfRelativeLevel A T β
  have hr : Set.range f.left ⊆ Set.range (Locus.LevelCover.fullFrameOpen A p (N := N)).ι := by
    rw [Scheme.Opens.range_ι]
    exact relativeLevel_frame_range A p T f β
  let l := IsOpenImmersion.lift (Locus.LevelCover.fullFrameOpen A p).ι f.left hr
  have hl : l ≫ (Locus.LevelCover.fullFrameOpen A p).ι = f.left := IsOpenImmersion.lift_fac _ _ hr
  refine Over.homMk l ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ (Level.Cover.LevelCover.frameScheme A N).hom) hl).trans f.w)

theorem fullFrameOfRelativeLevel_inclusion [NeZero N] (T : Over S)
    (β : (A.pullback T.hom).FullLevel N) :
    fullFrameOfRelativeLevel A p T β ≫ Finite.Monomorphisms.LevelCover.fullFrameInclusion A p = IndependentFrames.LevelCover.frameOfRelativeLevel A T β := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (Locus.LevelCover.fullFrameOpen A p (N := N)).ι
    (IndependentFrames.LevelCover.frameOfRelativeLevel A T β).left _

end

/-! Finite etale representability of full ordered levels on an arbitrary
characteristic-zero abelian scheme. Neither a global level nor a
representability hypothesis is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K)) [NeZero N]

instance fullFrameInclusion_mono : Mono (Finite.Monomorphisms.LevelCover.fullFrameInclusion A p (N := N)) := by
  let : Mono (Finite.Monomorphisms.LevelCover.fullFrameInclusion A p (N := N)).left :=
    inferInstanceAs (Mono (Locus.LevelCover.fullFrameOpen A p (N := N)).ι)
  exact Over.mono_of_mono_left _

/-- The constructed full-frame scheme classifies full levels on every
test scheme, with its canonical universal coefficient map. -/
def fullFramePointsEquiv (T : Over S) :
    (T ⟶ Locus.LevelCover.fullFrameScheme A p (N := N)) ≃ (A.pullback T.hom).FullLevel N where
  toFun f := (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p).restrict f
  invFun β := fullFrameOfRelativeLevel A p T β
  left_inv f := by
    apply (cancel_mono (Finite.Monomorphisms.LevelCover.fullFrameInclusion A p)).mp
    exact (fullFrameOfRelativeLevel_inclusion A p T _).trans
      ((FrameRestriction.LevelCover.frameOfRelativeLevel_restrict A f _).trans
        (congrArg (fun q => f ≫ q) (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel_classifying A p)))
  right_inv β := by
    apply FrameRestriction.LevelCover.frameOfRelativeLevel_injective A T
    exact (FrameRestriction.LevelCover.frameOfRelativeLevel_restrict A (fullFrameOfRelativeLevel A p T β) _).trans
      ((congrArg (fun q => fullFrameOfRelativeLevel A p T β ≫ q)
        (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel_classifying A p)).trans
          (fullFrameOfRelativeLevel_inclusion A p T β))

theorem fullFramePointsEquiv_classifying (T : Over S)
    (f : T ⟶ Locus.LevelCover.fullFrameScheme A p (N := N)) :
    IndependentFrames.LevelCover.frameOfRelativeLevel A T (fullFramePointsEquiv A p T f) = f ≫ Finite.Monomorphisms.LevelCover.fullFrameInclusion A p :=
  (FrameRestriction.LevelCover.frameOfRelativeLevel_restrict A f _).trans
    (congrArg (fun q => f ≫ q) (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel_classifying A p))

/-- The classification commutes with the actual pullback and transport
maps of the full-level family functor. -/
theorem fullFramePointsEquiv_natural {T U : Over S} (j : T ⟶ U)
    (f : U ⟶ Locus.LevelCover.fullFrameScheme A p (N := N)) :
    fullFramePointsEquiv A p T (j ≫ f) = (fullFramePointsEquiv A p U f).restrict j := by
  apply FrameRestriction.LevelCover.frameOfRelativeLevel_injective A T
  exact (fullFramePointsEquiv_classifying A p T (j ≫ f)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => j ≫ q) (fullFramePointsEquiv_classifying A p U f).symm).trans
        (FrameRestriction.LevelCover.frameOfRelativeLevel_restrict A j _).symm))

def fullLevelRepresentable :
    (FrameRestriction.LevelCover.fullLevelFamilyFunctor A (N := N)).RepresentableBy (Locus.LevelCover.fullFrameScheme A p (N := N)) where
  homEquiv {T} := fullFramePointsEquiv A p T
  homEquiv_comp j f := fullFramePointsEquiv_natural A p j f

include p in
/-- Every characteristic-zero abelian scheme has an actual finite
etale parameter scheme for all full levels at each nonzero level. -/
theorem finite_etale_fullLevel_parameter :
    ∃ F : Over S, IsFinite F.hom ∧ Etale F.hom ∧
      Nonempty ((FrameRestriction.LevelCover.fullLevelFamilyFunctor A (N := N)).RepresentableBy F) :=
  ⟨Locus.LevelCover.fullFrameScheme A p, (Locus.LevelCover.fullFrameScheme_finite_etale A p).1,
    (Locus.LevelCover.fullFrameScheme_finite_etale A p).2, ⟨fullLevelRepresentable A p⟩⟩

theorem fullLevel_unique_fullFrame_classifying (T : Over S)
    (β : (A.pullback T.hom).FullLevel N) :
    ∃! f : T ⟶ Locus.LevelCover.fullFrameScheme A p (N := N),
      (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p).restrict f = β := by
  refine ⟨(fullFramePointsEquiv A p T).symm β, (fullFramePointsEquiv A p T).apply_symm_apply β, ?_⟩
  intro f hf
  exact (fullFramePointsEquiv A p T).injective
    (hf.trans ((fullFramePointsEquiv A p T).apply_symm_apply β).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Factorization.LevelCover
