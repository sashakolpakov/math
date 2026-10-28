import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange

/-! # Split Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitFrames.LevelCover

noncomputable section

/-! The split frame cover: locally constant changes of basis construct
actual morphisms into the frame scheme, inverse to reading its labels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem coefficientHom_one {G : Type*} [CommGroup G] (a : G) (ha : a ^ N = 1) :
    Finite.Frames.LevelCover.coefficientHom a ha (1 : ZMod N) = Additive.ofMul a := by
  unfold Finite.Frames.LevelCover.coefficientHom
  simpa using (ZMod.lift_coe N ⟨zmultiplesHom (Additive G) (Additive.ofMul a), _⟩ (1 : ℤ))

theorem frameHom_standard {G : Type*} [CommGroup G]
    (a : Fin (2 * g) → G) (ha : ∀ i, a i ^ N = 1) (j : Fin (2 * g)) :
    Finite.Frames.LevelCover.frameHom a ha (Frame.Map.LevelCover.standardLevelVector j) = a j := by
  simp [Finite.Frames.LevelCover.frameHom, Frame.Map.LevelCover.standardLevelVector, AddMonoidHom.toMultiplicativeLeft,
    Pi.single_apply, apply_ite, coefficientHom_one]

def labelsHom (T : Over S)
    (b : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N)) :
    Frame.Labels.LevelCover.Coefficients g N →* LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N) where
  toFun c := b.map (fun e => e c)
  map_one' := by apply LocallyConstant.ext; intro x; exact map_one (b x)
  map_mul' c d := by apply LocallyConstant.ext; intro x; exact map_mul (b x) c d

def labeledTorsionHom (α : A.FullLevel N) (T : Over S)
    (b : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N)) :
    Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T :=
  ((α.hom.app (.op T)).hom).comp (labelsHom T b)

def torsionHomTuple (T : Over S) (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) :
    T ⟶ Level.Cover.LevelCover.torsionTuples A N :=
  Pi.lift (fun i => (Level.Cover.LevelCover.torsionPointsEquiv A N T).symm
    ⟨(h (Frame.Map.LevelCover.standardLevelVector i)).val, (h (Frame.Map.LevelCover.standardLevelVector i)).property⟩)

theorem torsionHomTuple_coordinate (T : Over S)
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) (i : Fin (2 * g)) :
    torsionHomTuple A T h ≫ Level.Cover.LevelCover.coordinate A N i = (h (Frame.Map.LevelCover.standardLevelVector i)).val := by
  change Pi.lift _ ≫ (Pi.π (fun _ : Fin (2 * g) => Level.Cover.LevelCover.torsion A N) i ≫
    Level.Cover.LevelCover.torsionInclusion A N) = _
  rw [← Category.assoc, Pi.lift_comp_π]
  exact congrArg Subtype.val ((Level.Cover.LevelCover.torsionPointsEquiv A N T).apply_symm_apply _)

theorem torsionHomTuple_relation [NeZero N] (T : Over S)
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N T) (c : Frame.Labels.LevelCover.Coefficients g N) :
    torsionHomTuple A T h ≫ Level.Cover.LevelCover.relation A N c.toAdd = (h c).val := by
  calc
    _ = ∏ i, (torsionHomTuple A T h ≫ Level.Cover.LevelCover.coordinate A N i) ^ (c.toAdd i).val := by
      change A.pointsPullback (torsionHomTuple A T h) (∏ i, _) = _
      rw [map_prod]
      simp only [map_pow, HilbertConstruction.Abelian.Schemes.AbelianScheme.pointsPullback_apply]
    _ = ∏ i, (h (Frame.Map.LevelCover.standardLevelVector i)).val ^ (c.toAdd i).val := by
      simp only [torsionHomTuple_coordinate]
    _ = (h c).val := by
      have hc : c = ∏ i, Frame.Map.LevelCover.standardLevelVector (N := N) i ^ (c.toAdd i).val :=
        Frame.Map.LevelCover.level_vector_decomposition c.toAdd
      simpa only [map_pow, MonoidHom.coe_comp, Function.comp_apply, Subgroup.subtype_apply] using
        (map_prod ((A.torsionPoints N T).subtype.comp h) _ _).symm.trans
          (congrArg (fun d => (h d).val) hc.symm)

theorem labeledTorsionHom_pullback_injective (α : A.FullLevel N) (T : Over S)
    (b : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N))
    {U : Over S} [Nonempty U.left] (j : U ⟶ T) :
    Function.Injective ((A.torsionPullback N j).comp (labeledTorsionHom A α T b)) := by
  intro c d h
  have hn (e : Frame.Labels.LevelCover.Coefficients g N) :=
    ConcreteCategory.congr_hom (α.hom.naturality j.op) (labelsHom T b e)
  have heq : α.hom.app (.op U)
      ((labelsHom T b c).comap ⟨j.left, j.left.continuous⟩) =
    α.hom.app (.op U) ((labelsHom T b d).comap ⟨j.left, j.left.continuous⟩) :=
      (hn c).trans (h.trans (hn d).symm)
  have hlc := (α.app (.op U)).groupIsoToMulEquiv.injective heq
  let u : U.left := Classical.choice inferInstance
  exact (b (j.left u)).injective (congrArg (fun v : LocallyConstant U.left _ => v u) hlc)

theorem labeledTuple_mem_frame [NeZero N] (α : A.FullLevel N) (T : Over S)
    (b : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N)) (t : T.left) :
    (torsionHomTuple A T (labeledTorsionHom A α T b)).left t ∈ Level.Cover.LevelCover.frameOpen A N := by
  change (torsionHomTuple A T (labeledTorsionHom A α T b)).left t ∈
    (Level.Cover.LevelCover.frameOpen A N : Set (Level.Cover.LevelCover.torsionTuples A N).left)
  unfold Level.Cover.LevelCover.frameOpen
  rw [TopologicalSpace.Opens.coe_iInf]
  apply Set.mem_iInter.mpr
  intro c
  by_cases hc : c = 0
  · simp [hc]
  · rw [iInf_pos hc]
    change (torsionHomTuple A T (labeledTorsionHom A α T b)).left t ∉
      Set.range (Level.Cover.LevelCover.relationZeroInclusion A N c).left
    apply Frame.Map.LevelCover.tuple_avoids_relation A _ c ?_ t
    intro U _ j hz
    have hr := torsionHomTuple_relation A T (labeledTorsionHom A α T b) (Multiplicative.ofAdd c)
    change torsionHomTuple A T (labeledTorsionHom A α T b) ≫ Level.Cover.LevelCover.relation A N c = _ at hr
    rw [Category.assoc, hr] at hz
    have hz' : (A.torsionPullback N j).comp (labeledTorsionHom A α T b)
        (Multiplicative.ofAdd c) = 1 := Subtype.ext hz
    have heq := labeledTorsionHom_pullback_injective A α T b j
      (hz'.trans (map_one _).symm)
    exact hc (congrArg Multiplicative.toAdd heq)

def frameMapOfLabels [NeZero N] (α : A.FullLevel N) (T : Over S)
    (b : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N)) :
    T ⟶ Level.Cover.LevelCover.frameScheme A N := by
  let q := torsionHomTuple A T (labeledTorsionHom A α T b)
  have h : Set.range q.left ⊆ Set.range (Level.Cover.LevelCover.frameInclusion A N).left := by
    rintro _ ⟨t, rfl⟩
    change q.left t ∈ Set.range (Level.Cover.LevelCover.frameOpen A N).ι
    rw [Scheme.Opens.range_ι]
    exact labeledTuple_mem_frame A α T b t
  let f := IsOpenImmersion.lift (Level.Cover.LevelCover.frameInclusion A N).left q.left h
  have hf : f ≫ (Level.Cover.LevelCover.frameInclusion A N).left = q.left := IsOpenImmersion.lift_fac _ _ h
  refine Over.homMk f ?_
  change f ≫ (Level.Cover.LevelCover.frameInclusion A N).left ≫ (Level.Cover.LevelCover.torsionTuples A N).hom = T.hom
  rw [← Category.assoc, hf]
  exact q.w

@[simp] theorem frameMapOfLabels_forget [NeZero N] (α : A.FullLevel N) (T : Over S)
    (b : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N)) :
    frameMapOfLabels A α T b ≫ Level.Cover.LevelCover.frameInclusion A N =
      torsionHomTuple A T (labeledTorsionHom A α T b) := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem frameTorsionHom_frameMapOfLabels [NeZero N] (α : A.FullLevel N) (T : Over S)
    (b : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N))
    (c : Frame.Labels.LevelCover.Coefficients g N) :
    Frame.Labels.LevelCover.frameTorsionHom A T (frameMapOfLabels A α T b) c = labeledTorsionHom A α T b c := by
  apply Subtype.ext
  rw [Frame.Labels.LevelCover.frameTorsionHom_val, frameMapOfLabels_forget, torsionHomTuple_relation]

@[simp] theorem frameChangeLabels_frameMapOfLabels [NeZero N] (α : A.FullLevel N) (T : Over S)
    (b : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N)) :
    Frame.Labels.LevelCover.frameChangeLabels A α T (frameMapOfLabels A α T b) = b := by
  apply LocallyConstant.ext
  intro t
  apply MulEquiv.ext
  intro c
  have h : Frame.Labels.LevelCover.frameChangeHom A α T (frameMapOfLabels A α T b) c = labelsHom T b c := by
    change α.inv.app (.op T) (Frame.Labels.LevelCover.frameTorsionHom A T (frameMapOfLabels A α T b) c) = _
    rw [frameTorsionHom_frameMapOfLabels]
    exact (α.app (.op T)).groupIsoToMulEquiv.symm_apply_apply _
  exact congrArg (fun d : LocallyConstant T.left _ => d t) h

theorem labeledTorsionHom_frameChangeLabels [NeZero N] (α : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (c : Frame.Labels.LevelCover.Coefficients g N) :
    labeledTorsionHom A α T (Frame.Labels.LevelCover.frameChangeLabels A α T f) c = Frame.Labels.LevelCover.frameTorsionHom A T f c := by
  have h : labelsHom T (Frame.Labels.LevelCover.frameChangeLabels A α T f) c = Frame.Labels.LevelCover.frameChangeHom A α T f c := by
    apply LocallyConstant.ext
    intro t
    rfl
  change α.hom.app (.op T) (labelsHom T (Frame.Labels.LevelCover.frameChangeLabels A α T f) c) = _
  rw [h]
  exact (α.app (.op T)).groupIsoToMulEquiv.apply_symm_apply _

@[simp] theorem frameMapOfLabels_frameChangeLabels [NeZero N] (α : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    frameMapOfLabels A α T (Frame.Labels.LevelCover.frameChangeLabels A α T f) = f := by
  suffices h : frameMapOfLabels A α T (Frame.Labels.LevelCover.frameChangeLabels A α T f) ≫ Level.Cover.LevelCover.frameInclusion A N =
      f ≫ Level.Cover.LevelCover.frameInclusion A N by
    apply Over.OverMorphism.ext
    apply (cancel_mono (Level.Cover.LevelCover.frameInclusion A N).left).mp
    exact congrArg (fun q => q.left) h
  rw [frameMapOfLabels_forget]
  apply Pi.hom_ext
  intro i
  apply (Level.Cover.LevelCover.torsionPointsEquiv A N T).injective
  apply Subtype.ext
  change torsionHomTuple A T (labeledTorsionHom A α T (Frame.Labels.LevelCover.frameChangeLabels A α T f)) ≫
    Level.Cover.LevelCover.coordinate A N i = (f ≫ Level.Cover.LevelCover.frameInclusion A N) ≫ Level.Cover.LevelCover.coordinate A N i
  rw [torsionHomTuple_coordinate, labeledTorsionHom_frameChangeLabels]
  change Finite.Frames.LevelCover.frameHom _ _ (Frame.Map.LevelCover.standardLevelVector i) = _
  rw [frameHom_standard]
  exact (Category.assoc _ _ _).symm

/-- On a trivialized base the frame scheme represents locally constant
changes of basis, with explicit mutually inverse constructions. -/
def splitFramePointsEquiv [NeZero N] (α : A.FullLevel N) (T : Over S) :
    (T ⟶ Level.Cover.LevelCover.frameScheme A N) ≃
      LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N) where
  toFun := Frame.Labels.LevelCover.frameChangeLabels A α T
  invFun := frameMapOfLabels A α T
  left_inv := frameMapOfLabels_frameChangeLabels A α T
  right_inv := frameChangeLabels_frameMapOfLabels A α T

theorem frameChangeLabels_natural [NeZero N] (α : A.FullLevel N) {T U : Over S}
    (j : U ⟶ T) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    Frame.Labels.LevelCover.frameChangeLabels A α U (j ≫ f) =
      (Frame.Labels.LevelCover.frameChangeLabels A α T f).comap ⟨j.left, j.left.continuous⟩ := by
  apply LocallyConstant.ext
  intro u
  apply MulEquiv.ext
  intro c
  exact congrArg (fun d : LocallyConstant U.left _ => d u)
    (Frame.Labels.LevelCover.frameChangeHom_natural A α j f c)

/-- The pointwise equivalences are natural, so they establish the
universal property of the split frame scheme on all test schemes. -/
def splitFrameRepresentable [NeZero N] (α : A.FullLevel N) :
    (HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N) ⋙
      forget GrpCat).RepresentableBy (Level.Cover.LevelCover.frameScheme A N) where
  homEquiv := splitFramePointsEquiv A α _
  homEquiv_comp j f := frameChangeLabels_natural A α j f

def constantFrameRepresentable :
    (HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N) ⋙
      forget GrpCat).RepresentableBy
      (HilbertConstruction.ConstantScheme.Iff.constantScheme S (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N)) where
  homEquiv := HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S _ _
  homEquiv_comp _ _ := rfl

/-- The actual split frame scheme is the disjoint union indexed by
automorphisms of the finite standard level module. -/
def splitFrameSchemeIso [NeZero N] (α : A.FullLevel N) :
    Level.Cover.LevelCover.frameScheme A N ≅ HilbertConstruction.ConstantScheme.Iff.constantScheme S (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N) :=
  (splitFrameRepresentable A α).uniqueUpToIso constantFrameRepresentable

/-- The frame scheme parametrizes all full levels on every actual
pullback of A, not just changes of basis on its original base. -/
def fullLevelParameterEquiv [NeZero N] (α : A.FullLevel N) (T : Over S) :
    (T ⟶ Level.Cover.LevelCover.frameScheme A N) ≃ (A.pullback T.hom).FullLevel N :=
  (splitFramePointsEquiv A α T).trans
    ((HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoEquiv (S := T.left) (G := Frame.Labels.LevelCover.Coefficients g N)
      (H := Frame.Labels.LevelCover.Coefficients g N)).symm.trans (Level.Data.framesEquivAut (α.pullback T.hom)).symm)

@[simp] theorem fullLevelParameterEquiv_apply [NeZero N] (α : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    fullLevelParameterEquiv A α T f = Frame.Labels.LevelCover.fullLevelFromFrame A α T f := rfl

/-- Existence and uniqueness of the classifying map for every full level
on a test pullback, proved from the explicit label equivalences. -/
theorem fullLevel_unique_classifying_map [NeZero N] (α : A.FullLevel N) (T : Over S)
    (β : (A.pullback T.hom).FullLevel N) :
    ∃! f : T ⟶ Level.Cover.LevelCover.frameScheme A N, Frame.Labels.LevelCover.fullLevelFromFrame A α T f = β := by
  let e := fullLevelParameterEquiv A α T
  refine ⟨e.symm β, e.apply_symm_apply β, ?_⟩
  intro f hf
  exact e.injective (hf.trans (e.apply_symm_apply β).symm)

/-- The split frame-cover construction is compatible with arbitrary
base change via the constant-scheme presentation. -/
def splitFrameBaseChangeIso [NeZero N] (α : A.FullLevel N) {S' : Scheme} (u : S' ⟶ S) :
    Level.Cover.LevelCover.frameScheme (A.pullback u) N ≅ (Over.pullback u).obj (Level.Cover.LevelCover.frameScheme A N) :=
  splitFrameSchemeIso (A.pullback u) (α.pullback u) ≪≫
    HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso u (Frame.Labels.LevelCover.Coefficients g N ≃* Frame.Labels.LevelCover.Coefficients g N) ≪≫
      (Over.pullback u).mapIso (splitFrameSchemeIso A α).symm

/-- Completed split relative-level bridge: an actual finite etale
surjective scheme, a universal full level, and its classifying equivalence
on all base schemes. -/
theorem finite_etale_fullLevel_cover [NeZero N] (α : A.FullLevel N) :
    IsFinite (Level.Cover.LevelCover.frameScheme A N).hom ∧ Etale (Level.Cover.LevelCover.frameScheme A N).hom ∧
      Surjective (Level.Cover.LevelCover.frameScheme A N).hom ∧
      ∀ (T : Over S) (β : (A.pullback T.hom).FullLevel N),
        ∃! f : T ⟶ Level.Cover.LevelCover.frameScheme A N, Frame.Labels.LevelCover.fullLevelFromFrame A α T f = β := by
  obtain ⟨hf, he, hs⟩ := Frame.Finiteness.LevelCover.frameScheme_split_cover A α
  exact ⟨hf, he, hs, fullLevel_unique_classifying_map A α⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitFrames.LevelCover
