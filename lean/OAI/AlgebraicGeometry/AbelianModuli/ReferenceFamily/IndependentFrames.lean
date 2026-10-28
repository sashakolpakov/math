import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.GroupScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitFrames

/-! # Independent Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IndependentFrames.LevelCover

noncomputable section

section

/-! Construct a map to the actual frame scheme from torsion sections
which remain independent after all changes of test scheme. This converse
does not require a global full level or a cardinality assumption. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

abbrev independentTuple (T : Over S) (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) :
    T ⟶ Level.Cover.LevelCover.torsionTuples A N := SplitFrames.LevelCover.torsionHomTuple A T h

theorem independentTuple_coordinate (T : Over S)
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) (i : Fin (2 * g)) :
    independentTuple A T h ≫ Level.Cover.LevelCover.coordinate A N i = (h (Frame.Map.LevelCover.standardLevelVector i)).val :=
  SplitFrames.LevelCover.torsionHomTuple_coordinate A T h i

theorem independentTuple_relation [NeZero N] (T : Over S)
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) (c : Fin (2 * g) → ZMod N) :
    independentTuple A T h ≫ Level.Cover.LevelCover.relation A N c = (h (Multiplicative.ofAdd c)).val :=
  SplitFrames.LevelCover.torsionHomTuple_relation A T h (Multiplicative.ofAdd c)

def StaysIndependent (T : Over S) (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) : Prop :=
  ∀ (W : Over S), Nonempty W.left → ∀ j : W ⟶ T,
    Function.Injective ((A.torsionPullback N j).comp h)

theorem independentTuple_mem [NeZero N] (T : Over S)
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) (hi : StaysIndependent A T h) (t : T.left) :
    (independentTuple A T h).left t ∈ Level.Cover.LevelCover.frameOpen A N := by
  change (independentTuple A T h).left t ∈
    ((⨅ c, ⨅ (_ : c ≠ 0), Level.Cover.LevelCover.relationNonzero A N c : (Level.Cover.LevelCover.torsionTuples A N).left.Opens) :
      Set (Level.Cover.LevelCover.torsionTuples A N).left)
  simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  intro c
  by_cases hc : c = 0
  · simp [hc]
  · rw [iInf_pos hc]
    apply Frame.Map.LevelCover.tuple_avoids_relation A (independentTuple A T h) c ?_ t
    intro W hW j hz
    have hz' : A.torsionPullback N j (h (Multiplicative.ofAdd c)) = 1 := by
      apply Subtype.ext
      change j ≫ (h (Multiplicative.ofAdd c)).val = 1
      exact (congrArg (fun f : T ⟶ A.scheme => j ≫ f)
        (independentTuple_relation A T h c)).symm.trans ((Category.assoc _ _ _).symm.trans hz)
    have hc' : Multiplicative.ofAdd c = (1 : Frame.Labels.LevelCover.Coefficients g N) :=
      hi W hW j (hz'.trans (map_one ((A.torsionPullback N j).comp h)).symm)
    exact hc (congrArg Multiplicative.toAdd hc')

def frameOfIndependent [NeZero N] (T : Over S)
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) (hi : StaysIndependent A T h) :
    T ⟶ Level.Cover.LevelCover.frameScheme A N := by
  have hr : Set.range (independentTuple A T h).left ⊆ Set.range (Level.Cover.LevelCover.frameInclusion A N).left := by
    rintro _ ⟨t, rfl⟩
    change (independentTuple A T h).left t ∈ Set.range (Level.Cover.LevelCover.frameOpen A N).ι
    rw [Scheme.Opens.range_ι]
    exact independentTuple_mem A T h hi t
  let q := IsOpenImmersion.lift (Level.Cover.LevelCover.frameInclusion A N).left (independentTuple A T h).left hr
  have hq : q ≫ (Level.Cover.LevelCover.frameInclusion A N).left = (independentTuple A T h).left :=
    IsOpenImmersion.lift_fac _ _ hr
  refine Over.homMk q ?_
  change q ≫ (Level.Cover.LevelCover.frameInclusion A N).left ≫ (Level.Cover.LevelCover.torsionTuples A N).hom = T.hom
  rw [← Category.assoc, hq]
  exact (independentTuple A T h).w

theorem frameOfIndependent_forget [NeZero N] (T : Over S)
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) (hi : StaysIndependent A T h) :
    frameOfIndependent A T h hi ≫ Level.Cover.LevelCover.frameInclusion A N = independentTuple A T h := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem frameOfIndependent_coefficients [NeZero N] (T : Over S)
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) (hi : StaysIndependent A T h) :
    Frame.Labels.LevelCover.frameTorsionHom A T (frameOfIndependent A T h hi) = h := by
  apply MonoidHom.ext
  intro c
  apply Subtype.ext
  rw [Frame.Labels.LevelCover.frameTorsionHom_val, frameOfIndependent_forget, independentTuple_relation]
  rfl

theorem frameTorsionHom_staysIndependent [NeZero N] (T : Over S)
    (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) : StaysIndependent A T (Frame.Labels.LevelCover.frameTorsionHom A T f) := by
  intro W hW j
  let : Nonempty W.left := hW
  have he : (A.torsionPullback N j).comp (Frame.Labels.LevelCover.frameTorsionHom A T f) =
      Frame.Labels.LevelCover.frameTorsionHom A W (j ≫ f) := MonoidHom.ext (Frame.Labels.LevelCover.frameTorsionHom_natural A j f)
  rw [he]
  exact Frame.GroupScheme.LevelCover.frameTorsionHom_injective A W (j ≫ f)

theorem independentTuple_frameTorsionHom (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    independentTuple A T (Frame.Labels.LevelCover.frameTorsionHom A T f) = f ≫ Level.Cover.LevelCover.frameInclusion A N := by
  apply Pi.hom_ext
  intro i
  apply (Level.Cover.LevelCover.torsionPointsEquiv A N T).injective
  apply Subtype.ext
  change independentTuple A T (Frame.Labels.LevelCover.frameTorsionHom A T f) ≫ Level.Cover.LevelCover.coordinate A N i =
    (f ≫ Level.Cover.LevelCover.frameInclusion A N) ≫ Level.Cover.LevelCover.coordinate A N i
  rw [independentTuple_coordinate]
  change Finite.Frames.LevelCover.frameHom _ _ (Frame.Map.LevelCover.standardLevelVector i) = _
  exact SplitFrames.LevelCover.frameHom_standard _ _ i

/-- The frame scheme represents precisely the torsion coefficient
systems that remain independent on every nonempty test. -/
def independentFramePointsEquiv [NeZero N] (T : Over S) :
    (T ⟶ Level.Cover.LevelCover.frameScheme A N) ≃
      {h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T // StaysIndependent A T h} where
  toFun f := ⟨Frame.Labels.LevelCover.frameTorsionHom A T f, frameTorsionHom_staysIndependent A T f⟩
  invFun h := frameOfIndependent A T h.val h.property
  left_inv f := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (Level.Cover.LevelCover.frameInclusion A N).left).mp
    exact congrArg Over.Hom.left ((frameOfIndependent_forget A T _ _).trans
      (independentTuple_frameTorsionHom A T f))
  right_inv h := Subtype.ext (frameOfIndependent_coefficients A T h.val h.property)

end

/-! A relative full level on A over a test scheme determines an actual
map to the original frame scheme. No level on the original base is used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def testLiftIso (T W : Over S) (j : W ⟶ T) :
    (Over.map T.hom).obj (Over.mk j.left) ≅ W :=
  Over.isoMk (Iso.refl W.left) ((Category.id_comp _).trans j.w.symm)

def relativePointEquiv (T W : Over S) (j : W ⟶ T) :
    (A.pullback T.hom).torsionPoints N (Over.mk j.left) ≃* A.torsionPoints N W :=
  (A.torsionBaseChangeEquiv T.hom (Over.mk j.left) N).trans
    (((A.torsionFunctor N).mapIso (testLiftIso T W j).op).symm.groupIsoToMulEquiv)

theorem relativePointEquiv_left (T W : Over S) (j : W ⟶ T)
    (x : (A.pullback T.hom).torsionPoints N (Over.mk j.left)) :
    (relativePointEquiv A T W j x).val.left = x.val.left ≫ pullback.fst A.scheme.hom T.hom :=
  Category.id_comp _

def testLiftToBase (T W : Over S) (j : W ⟶ T) :
    Over.mk j.left ⟶ ConstantSectionsOn.ConstantSections.baseTest T.left := Over.homMk j.left (Category.comp_id _)

theorem relativePointEquiv_natural (T W : Over S) (j : W ⟶ T)
    (x : (A.pullback T.hom).torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest T.left)) :
    relativePointEquiv A T W j
      ((A.pullback T.hom).torsionPullback N (testLiftToBase T W j) x) =
      A.torsionPullback N j (relativePointEquiv A T T (𝟙 T) x) := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change (relativePointEquiv A T W j
      ((A.pullback T.hom).torsionPullback N (testLiftToBase T W j) x)).val.left =
    j.left ≫ (relativePointEquiv A T T (𝟙 T) x).val.left
  rw [relativePointEquiv_left, relativePointEquiv_left]
  exact Category.assoc j.left x.val.left (pullback.fst A.scheme.hom T.hom)

def relativeCoefficients (T : Over S)
    (α : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶ (A.pullback T.hom).torsionFunctor N) :
    Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T :=
  (relativePointEquiv A T T (𝟙 T)).toMonoidHom.comp
    ((α.app (.op (ConstantSectionsOn.ConstantSections.baseTest T.left))).hom.comp LocallyConstant.constMonoidHom)

theorem relativeCoefficients_natural (T W : Over S) (j : W ⟶ T)
    (α : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶ (A.pullback T.hom).torsionFunctor N)
    (c : Frame.Labels.LevelCover.Coefficients g N) :
    A.torsionPullback N j (relativeCoefficients A T α c) =
      relativePointEquiv A T W j (α.app (.op (Over.mk j.left)) (LocallyConstant.const W.left c)) := by
  have hn := ConcreteCategory.congr_hom (α.naturality (testLiftToBase T W j).op)
    (LocallyConstant.const T.left c)
  change α.app (.op (Over.mk j.left)) (LocallyConstant.const W.left c) =
    (A.pullback T.hom).torsionPullback N (testLiftToBase T W j)
      (α.app (.op (ConstantSectionsOn.ConstantSections.baseTest T.left)) (LocallyConstant.const T.left c)) at hn
  exact (relativePointEquiv_natural A T W j _).symm.trans
    (congrArg (relativePointEquiv A T W j) hn.symm)

theorem relativeCoefficients_staysIndependent (T : Over S)
    (α : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶ (A.pullback T.hom).torsionFunctor N)
    (hinj : ∀ U : Over T.left, Function.Injective (α.app (.op U))) :
    StaysIndependent A T (relativeCoefficients A T α) := by
  intro W hW j c d hcd
  have he : relativePointEquiv A T W j
      (α.app (.op (Over.mk j.left)) (LocallyConstant.const W.left c)) =
    relativePointEquiv A T W j
      (α.app (.op (Over.mk j.left)) (LocallyConstant.const W.left d)) :=
    (relativeCoefficients_natural A T W j α c).symm.trans
      (hcd.trans (relativeCoefficients_natural A T W j α d))
  have hc := hinj (Over.mk j.left) ((relativePointEquiv A T W j).injective he)
  exact congrArg (fun f : LocallyConstant W.left (Frame.Labels.LevelCover.Coefficients g N) => f (Classical.choice hW)) hc

/-- An injective relative coefficient-system map is classified by an
actual morphism into the original frame scheme. -/
def frameOfRelativeMap [NeZero N] (T : Over S)
    (α : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶ (A.pullback T.hom).torsionFunctor N)
    (hinj : ∀ U : Over T.left, Function.Injective (α.app (.op U))) : T ⟶ Level.Cover.LevelCover.frameScheme A N :=
  frameOfIndependent A T (relativeCoefficients A T α)
    (relativeCoefficients_staysIndependent A T α hinj)

def frameOfRelativeLevel [NeZero N] (T : Over S) (α : (A.pullback T.hom).FullLevel N) :
    T ⟶ Level.Cover.LevelCover.frameScheme A N :=
  frameOfRelativeMap A T α.hom (fun U => (α.app (.op U)).groupIsoToMulEquiv.injective)

theorem frameOfRelativeMap_coefficients [NeZero N] (T : Over S)
    (α : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶ (A.pullback T.hom).torsionFunctor N)
    (hinj : ∀ U : Over T.left, Function.Injective (α.app (.op U))) :
    Frame.Labels.LevelCover.frameTorsionHom A T (frameOfRelativeMap A T α hinj) = relativeCoefficients A T α :=
  frameOfIndependent_coefficients A T _ _

theorem relativePointEquiv_frameAtBaseHom (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (c : Frame.Labels.LevelCover.Coefficients g N) :
    relativePointEquiv A T T (𝟙 T) (UniversalFrames.LevelCover.frameAtBaseHom A T f c) = Frame.Labels.LevelCover.frameTorsionHom A T f c := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [relativePointEquiv_left]
  have h := (A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N).apply_symm_apply
    (A.torsionPullback N (Frame.Labels.LevelCover.identityTestTo T) (Frame.Labels.LevelCover.frameTorsionHom A T f c))
  exact (congrArg (fun x : A.torsionPoints N (Frame.Labels.LevelCover.identityTestOver T) => x.val.left) h).trans
    (Category.id_comp _)

theorem relativeCoefficients_frameLevelMap (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    relativeCoefficients A T (UniversalFrames.LevelCover.frameLevelMap A T f) = Frame.Labels.LevelCover.frameTorsionHom A T f := by
  apply MonoidHom.ext
  intro c
  have h := UniversalFrames.LevelCover.torsionSectionExtension_const (A.pullback T.hom) (UniversalFrames.LevelCover.frameAtBaseHom A T f) c
  exact (congrArg (relativePointEquiv A T T (𝟙 T)) h).trans
    (relativePointEquiv_frameAtBaseHom A T f c)

/-- Reconstructing the relative natural map recovers every component,
by its values on constant vectors and the proved extension uniqueness. -/
theorem frameLevelMap_frameOfRelativeMap [NeZero N] (T : Over S)
    (α : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶ (A.pullback T.hom).torsionFunctor N)
    (hinj : ∀ U : Over T.left, Function.Injective (α.app (.op U))) :
    UniversalFrames.LevelCover.frameLevelMap A T (frameOfRelativeMap A T α hinj) = α := by
  apply UniversalFrames.LevelCover.torsionNatTrans_ext_on_constants
  intro c
  apply (relativePointEquiv A T T (𝟙 T)).injective
  change relativeCoefficients A T (UniversalFrames.LevelCover.frameLevelMap A T (frameOfRelativeMap A T α hinj)) c =
    relativeCoefficients A T α c
  rw [relativeCoefficients_frameLevelMap, frameOfRelativeMap_coefficients]

/-- The all-test frame functor is represented by the actual frame
scheme, without choosing a global torsion marking. -/
def relativeFramePointsEquiv [NeZero N] (T : Over S) :
    (T ⟶ Level.Cover.LevelCover.frameScheme A N) ≃
      {α : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶
        (A.pullback T.hom).torsionFunctor N //
          ∀ U : Over T.left, Function.Injective (α.app (.op U))} where
  toFun f := ⟨UniversalFrames.LevelCover.frameLevelMap A T f, Frame.GroupScheme.LevelCover.frameLevelMap_injective A T f⟩
  invFun α := frameOfRelativeMap A T α.val α.property
  left_inv f := by
    apply (independentFramePointsEquiv A T).injective
    apply Subtype.ext
    exact (frameOfRelativeMap_coefficients A T _ _).trans
      (relativeCoefficients_frameLevelMap A T f)
  right_inv α := Subtype.ext (frameLevelMap_frameOfRelativeMap A T α.val α.property)

/-- A relative full level has a unique actual classifying frame map,
even when the original abelian scheme has no global level structure. -/
theorem exists_unique_relativeLevel_frame [NeZero N] (T : Over S)
    (α : (A.pullback T.hom).FullLevel N) :
    ∃! f : T ⟶ Level.Cover.LevelCover.frameScheme A N, UniversalFrames.LevelCover.frameLevelMap A T f = α.hom := by
  refine ⟨frameOfRelativeLevel A T α, frameLevelMap_frameOfRelativeMap A T _ _, ?_⟩
  intro f hf
  apply (relativeFramePointsEquiv A T).injective
  apply Subtype.ext
  exact hf.trans (frameLevelMap_frameOfRelativeMap A T _ _).symm

/-- Full levels are exactly those classifying frame maps for which the
constructed universal coefficient map is an isomorphism. -/
def fullLevelFrameIsoEquiv [NeZero N] (T : Over S) :
    (A.pullback T.hom).FullLevel N ≃
      {f : T ⟶ Level.Cover.LevelCover.frameScheme A N // IsIso (UniversalFrames.LevelCover.frameLevelMap A T f)} where
  toFun α := ⟨frameOfRelativeLevel A T α, by
    have h := frameLevelMap_frameOfRelativeMap A T α.hom
      (fun U => (α.app (.op U)).groupIsoToMulEquiv.injective)
    change IsIso (UniversalFrames.LevelCover.frameLevelMap A T (frameOfRelativeMap A T α.hom _))
    rw [h]
    exact α.isIso_hom⟩
  invFun f := by
    letI := f.property
    exact asIso (UniversalFrames.LevelCover.frameLevelMap A T f.val)
  left_inv α := by
    apply Iso.ext
    exact frameLevelMap_frameOfRelativeMap A T α.hom
      (fun U => (α.app (.op U)).groupIsoToMulEquiv.injective)
  right_inv f := by
    apply Subtype.ext
    exact (relativeFramePointsEquiv A T).left_inv f.val

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IndependentFrames.LevelCover
