import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.Frames
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Map.LevelCover

noncomputable section

/-! A full level structure gives an actual morphism into the torsion-frame
locus. The construction uses naturality on all test schemes, so it also
excludes relations appearing only after a change of base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

/-- A constant level vector determines a torsion section on every test. -/
def levelSection (α : A.FullLevel N) (T : Over S) :
    Multiplicative (Fin (2 * g) → ZMod N) →* (T ⟶ A.scheme) :=
  (A.torsionPoints N T).subtype.comp
    (((α.hom.app (op T)).hom).comp LocallyConstant.constMonoidHom)

theorem levelSection_pow (α : A.FullLevel N) (T : Over S)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    levelSection A α T c ^ N = 1 :=
  (α.hom.app (op T) (LocallyConstant.const T.left c)).property

theorem levelSection_injective (α : A.FullLevel N) (T : Over S) [Nonempty T.left] :
    Function.Injective (levelSection A α T) := by
  intro c d h
  have h' : α.hom.app (op T) (LocallyConstant.const T.left c) =
      α.hom.app (op T) (LocallyConstant.const T.left d) := Subtype.ext h
  have hi : IsIso (α.hom.app (op T)) := by
    change IsIso ((α.app (op T)).hom)
    infer_instance
  have h'' := (ConcreteCategory.bijective_of_isIso (α.hom.app (op T))).injective h'
  exact congrArg (fun f : LocallyConstant T.left _ => f (Classical.choice inferInstance)) h''

theorem levelSection_natural (α : A.FullLevel N) {T U : Over S} (f : T ⟶ U)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    f ≫ levelSection A α U c = levelSection A α T c := by
  have h := ConcreteCategory.congr_hom (α.hom.naturality f.op)
    (LocallyConstant.const U.left c)
  exact (congrArg Subtype.val h).symm

def standardLevelVector (i : Fin (2 * g)) :
    Multiplicative (Fin (2 * g) → ZMod N) :=
  Multiplicative.ofAdd (Pi.single i 1)

theorem level_vector_decomposition [NeZero N] (c : Fin (2 * g) → ZMod N) :
    Multiplicative.ofAdd c = ∏ i, standardLevelVector (N := N) i ^ (c i).val := by
  apply Multiplicative.toAdd.injective
  change c = ∑ i, (c i).val • Pi.single i (1 : ZMod N)
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  simp

/-- The tuple of images of the standard basis under the full level. -/
def levelTuple (α : A.FullLevel N) (T : Over S) : T ⟶ Level.Cover.LevelCover.torsionTuples A N :=
  Pi.lift (fun i => (Level.Cover.LevelCover.torsionPointsEquiv A N T).symm
    ⟨levelSection A α T (standardLevelVector i), levelSection_pow A α T _⟩)

theorem levelTuple_coordinate (α : A.FullLevel N) (T : Over S) (i : Fin (2 * g)) :
    levelTuple A α T ≫ Level.Cover.LevelCover.coordinate A N i = levelSection A α T (standardLevelVector i) := by
  change Pi.lift _ ≫ (Pi.π (fun _ : Fin (2 * g) => Level.Cover.LevelCover.torsion A N) i ≫
    Level.Cover.LevelCover.torsionInclusion A N) = _
  rw [← Category.assoc, Pi.lift_comp_π]
  exact congrArg Subtype.val ((Level.Cover.LevelCover.torsionPointsEquiv A N T).apply_symm_apply _)

theorem levelTuple_relation [NeZero N] (α : A.FullLevel N) (T : Over S)
    (c : Fin (2 * g) → ZMod N) :
    levelTuple A α T ≫ Level.Cover.LevelCover.relation A N c = levelSection A α T (Multiplicative.ofAdd c) := by
  calc
    _ = ∏ i, (levelTuple A α T ≫ Level.Cover.LevelCover.coordinate A N i) ^ (c i).val := by
      change A.pointsPullback (levelTuple A α T) (∏ i, _) = _
      rw [map_prod]
      simp only [map_pow, HilbertConstruction.Abelian.Schemes.AbelianScheme.pointsPullback_apply]
    _ = ∏ i, levelSection A α T (standardLevelVector i) ^ (c i).val := by
      simp only [levelTuple_coordinate]
    _ = levelSection A α T (Multiplicative.ofAdd c) := by
      conv_rhs => rw [level_vector_decomposition c]
      simp only [map_prod, map_pow]

/-- A relation that remains nonzero on every nonempty test cannot meet
the closed subscheme where that relation vanishes. -/
theorem tuple_avoids_relation {T : Over S} (q : T ⟶ Level.Cover.LevelCover.torsionTuples A N)
    (c : Fin (2 * g) → ZMod N)
    (h : ∀ (W : Over S) [Nonempty W.left] (f : W ⟶ T),
      (f ≫ q) ≫ Level.Cover.LevelCover.relation A N c ≠ 1) (t : T.left) :
    q.left t ∉ Set.range (Level.Cover.LevelCover.relationZeroInclusion A N c).left := by
  rintro ⟨z, hz⟩
  let j := Level.Cover.LevelCover.relationZeroInclusion A N c
  let W : Over S := Over.mk (pullback.fst q.left j.left ≫ T.hom)
  let p : W ⟶ T := Over.homMk (pullback.fst q.left j.left) rfl
  let k : W ⟶ Level.Cover.LevelCover.relationZero A N c := Over.homMk (pullback.snd q.left j.left) (by
    change pullback.snd q.left j.left ≫ (Level.Cover.LevelCover.relationZero A N c).hom =
      pullback.fst q.left j.left ≫ T.hom
    rw [← j.w, ← q.w, ← Category.assoc, ← Category.assoc, pullback.condition])
  obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback t z hz.symm
  have : Nonempty W.left := ⟨w⟩
  apply h W p
  have hp : p ≫ q = k ≫ j := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  rw [hp, Category.assoc]
  have hj : j ≫ Level.Cover.LevelCover.relation A N c = 1 := by
    convert! (show (equalizer.ι (Level.Cover.LevelCover.relation A N c) (1 : Level.Cover.LevelCover.torsionTuples A N ⟶ A.scheme)) ≫
      Level.Cover.LevelCover.relation A N c = 1 from (by
        simpa only [MonObj.comp_one] using
          equalizer.condition (Level.Cover.LevelCover.relation A N c) (1 : Level.Cover.LevelCover.torsionTuples A N ⟶ A.scheme)))
  rw [hj, MonObj.comp_one]

theorem levelTuple_avoids_relation [NeZero N] (α : A.FullLevel N) (T : Over S)
    (t : T.left) (c : Fin (2 * g) → ZMod N) (hc : c ≠ 0) :
    (levelTuple A α T).left t ∉ Set.range (Level.Cover.LevelCover.relationZeroInclusion A N c).left := by
  apply tuple_avoids_relation A (levelTuple A α T) c ?_ t
  intro W _ f heq
  rw [Category.assoc, levelTuple_relation, levelSection_natural] at heq
  have heq' : levelSection A α W (Multiplicative.ofAdd c) =
      levelSection A α W 1 := heq.trans (map_one _).symm
  exact hc (congrArg Multiplicative.toAdd (levelSection_injective A α W heq'))

theorem levelTuple_mem_frameOpen [NeZero N] (α : A.FullLevel N) (T : Over S)
    (t : T.left) : (levelTuple A α T).left t ∈ Level.Cover.LevelCover.frameOpen A N := by
  change (levelTuple A α T).left t ∈
    ((⨅ c, ⨅ (_ : c ≠ 0), Level.Cover.LevelCover.relationNonzero A N c : (Level.Cover.LevelCover.torsionTuples A N).left.Opens) :
      Set (Level.Cover.LevelCover.torsionTuples A N).left)
  simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  intro c
  by_cases hc : c = 0
  · simp [hc]
  · rw [iInf_pos hc]
    change (levelTuple A α T).left t ∉ Set.range (Level.Cover.LevelCover.relationZeroInclusion A N c).left
    exact levelTuple_avoids_relation A α T t c hc

/-- The full level gives an actual scheme morphism into the added-level
frame locus, constructed by the open-immersion universal property. -/
def fullLevelFrameMap [NeZero N] (α : A.FullLevel N) (T : Over S) :
    T ⟶ Level.Cover.LevelCover.frameScheme A N := by
  have h : Set.range (levelTuple A α T).left ⊆ Set.range (Level.Cover.LevelCover.frameInclusion A N).left := by
    rintro _ ⟨t, rfl⟩
    change (levelTuple A α T).left t ∈ Set.range (Level.Cover.LevelCover.frameOpen A N).ι
    rw [Scheme.Opens.range_ι]
    exact levelTuple_mem_frameOpen A α T t
  let f := IsOpenImmersion.lift (Level.Cover.LevelCover.frameInclusion A N).left (levelTuple A α T).left h
  have hf : f ≫ (Level.Cover.LevelCover.frameInclusion A N).left = (levelTuple A α T).left :=
    IsOpenImmersion.lift_fac _ _ h
  refine Over.homMk f ?_
  change f ≫ (Level.Cover.LevelCover.frameInclusion A N).left ≫
      (Level.Cover.LevelCover.torsionTuples A N).hom = T.hom
  rw [← Category.assoc, hf]
  exact (levelTuple A α T).w

@[simp] theorem fullLevelFrameMap_forget [NeZero N] (α : A.FullLevel N) (T : Over S) :
    fullLevelFrameMap A α T ≫ Level.Cover.LevelCover.frameInclusion A N = levelTuple A α T := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem levelTuple_natural (α : A.FullLevel N) {T U : Over S} (f : T ⟶ U) :
    f ≫ levelTuple A α U = levelTuple A α T := by
  apply Pi.hom_ext
  intro i
  apply (Level.Cover.LevelCover.torsionPointsEquiv A N T).injective
  apply Subtype.ext
  change (f ≫ levelTuple A α U) ≫ Level.Cover.LevelCover.coordinate A N i =
    levelTuple A α T ≫ Level.Cover.LevelCover.coordinate A N i
  rw [Category.assoc, levelTuple_coordinate, levelTuple_coordinate, levelSection_natural]

/-- The constructed frame map commutes with every morphism of tests. -/
theorem fullLevelFrameMap_natural [NeZero N] (α : A.FullLevel N)
    {T U : Over S} (f : T ⟶ U) :
    f ≫ fullLevelFrameMap A α U = fullLevelFrameMap A α T := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (Level.Cover.LevelCover.frameInclusion A N).left).mp
  change (f ≫ fullLevelFrameMap A α U ≫ Level.Cover.LevelCover.frameInclusion A N).left =
    (fullLevelFrameMap A α T ≫ Level.Cover.LevelCover.frameInclusion A N).left
  rw [fullLevelFrameMap_forget, fullLevelFrameMap_forget, levelTuple_natural]

/-- Specifying the torsion generators determines the map to the frame
scheme uniquely. -/
theorem fullLevelFrameMap_unique [NeZero N] (α : A.FullLevel N) (T : Over S)
    (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (hf : f ≫ Level.Cover.LevelCover.frameInclusion A N = levelTuple A α T) :
    f = fullLevelFrameMap A α T := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (Level.Cover.LevelCover.frameInclusion A N).left).mp
  exact congrArg (fun q => q.left) (hf.trans (fullLevelFrameMap_forget A α T).symm)

/-- A chosen full level supplies a section of the actual frame scheme
over its base. -/
theorem frame_projection_has_section [NeZero N] (α : A.FullLevel N) :
    ∃ f : S ⟶ (Level.Cover.LevelCover.frameScheme A N).left, f ≫ (Level.Cover.LevelCover.frameScheme A N).hom = 𝟙 S :=
  ⟨(fullLevelFrameMap A α (Over.mk (𝟙 S))).left,
    (fullLevelFrameMap A α (Over.mk (𝟙 S))).w⟩

theorem frame_projection_surjective_of_fullLevel [NeZero N] (α : A.FullLevel N) :
    Surjective (Level.Cover.LevelCover.frameScheme A N).hom := by
  obtain ⟨f, hf⟩ := frame_projection_has_section A α
  constructor
  intro s
  exact ⟨f s, congrArg (fun q : S ⟶ S => q s) hf⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Map.LevelCover
