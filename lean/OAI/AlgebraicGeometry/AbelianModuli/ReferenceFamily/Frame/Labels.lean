import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Finiteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Data

/-! # Labels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover

noncomputable section

/-! Over a chosen torsion trivialization, the universal independent frame
gives a locally constant change of basis. The invertibility is proved by
testing relations on nonempty open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Topology

abbrev Coefficients (g N : ℕ) := Multiplicative (Fin (2 * g) → ZMod N)

theorem coefficients_pow {g N : ℕ} (c : Coefficients g N) : c ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  change N • c.toAdd = 0
  ext i
  simp [nsmul_eq_mul]

variable {S : Scheme} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def frameSectionHom (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    Coefficients g N →* (T ⟶ A.scheme) :=
  ReferenceFamily.Finite.Frames.LevelCover.frameHom (fun i => f ≫ Level.Cover.LevelCover.frameInclusion A N ≫ Level.Cover.LevelCover.coordinate A N i)
    (fun i => by rw [← MonObj.comp_pow, Level.Cover.LevelCover.frame_coordinate_pow, MonObj.comp_one])

theorem frameSectionHom_torsion (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (c : Coefficients g N) : frameSectionHom A T f c ^ N = 1 :=
  (map_pow (frameSectionHom A T f) c N).symm.trans
    ((congrArg (frameSectionHom A T f) (coefficients_pow c)).trans (map_one _))

def frameTorsionHom (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    Coefficients g N →* A.torsionPoints N T where
  toFun c := ⟨frameSectionHom A T f c, frameSectionHom_torsion A T f c⟩
  map_one' := Subtype.ext (map_one (frameSectionHom A T f))
  map_mul' c d := Subtype.ext (map_mul (frameSectionHom A T f) c d)

theorem frameTorsionHom_val [NeZero N] (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (c : Coefficients g N) :
    (frameTorsionHom A T f c).val = (f ≫ Level.Cover.LevelCover.frameInclusion A N) ≫ Level.Cover.LevelCover.relation A N c.toAdd := by
  change ReferenceFamily.Finite.Frames.LevelCover.frameHom _ _ (Multiplicative.ofAdd c.toAdd) = _
  rw [ReferenceFamily.Finite.Frames.LevelCover.frameHom_apply]
  change _ = A.pointsPullback (f ≫ Level.Cover.LevelCover.frameInclusion A N) (∏ i, Level.Cover.LevelCover.coordinate A N i ^ (c.toAdd i).val)
  rw [map_prod]
  simp only [map_pow, HilbertConstruction.Abelian.Schemes.AbelianScheme.pointsPullback_apply, Category.assoc]

theorem frameTorsionHom_natural [NeZero N] {T U : Over S}
    (j : U ⟶ T) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (c : Coefficients g N) :
    A.torsionPullback N j (frameTorsionHom A T f c) = frameTorsionHom A U (j ≫ f) c := by
  apply Subtype.ext
  change j ≫ (frameTorsionHom A T f c).val = (frameTorsionHom A U (j ≫ f) c).val
  rw [frameTorsionHom_val, frameTorsionHom_val]
  simp only [Category.assoc]

def frameChangeHom (α : A.FullLevel N) (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    Coefficients g N →* LocallyConstant T.left (Coefficients g N) :=
  ((α.inv.app (.op T)).hom).comp (frameTorsionHom A T f)

theorem frameChangeHom_natural [NeZero N] (α : A.FullLevel N) {T U : Over S}
    (j : U ⟶ T) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (c : Coefficients g N) :
    frameChangeHom A α U (j ≫ f) c =
      (frameChangeHom A α T f c).comap ⟨j.left, j.left.continuous⟩ := by
  have h := ConcreteCategory.congr_hom (α.inv.naturality j.op) (frameTorsionHom A T f c)
  change α.inv.app (.op U) (A.torsionPullback N j (frameTorsionHom A T f c)) = _ at h
  rw [frameTorsionHom_natural] at h
  exact h

def frameChangeAt (α : A.FullLevel N) (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (t : T.left) :
    Coefficients g N →* Coefficients g N :=
  (LocallyConstant.evalMonoidHom t).comp (frameChangeHom A α T f)

/-- Independence on every nonempty test forces the change-of-basis
matrix at each ordinary scheme point to be injective. -/
theorem frameChangeAt_injective [NeZero N] (α : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (t : T.left) :
    Function.Injective (frameChangeAt A α T f t) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro c hc
  change c = 1
  by_contra hne
  let d := frameChangeHom A α T f c
  let O : T.left.Opens := ⟨{x | d x = 1}, d.isLocallyConstant.isOpen_fiber 1⟩
  let U : Over S := Over.mk (O.ι ≫ T.hom)
  let j : U ⟶ T := Over.homMk O.ι rfl
  have ht : t ∈ O := hc
  have : Nonempty U.left := ⟨⟨t, ht⟩⟩
  have hz : frameChangeHom A α U (j ≫ f) c = 1 := by
    rw [frameChangeHom_natural]
    apply LocallyConstant.ext
    intro x
    exact x.property
  have hz' : frameTorsionHom A U (j ≫ f) c = 1 := by
    apply ((α.app (.op U)).symm.groupIsoToMulEquiv).injective
    exact hz.trans (map_one _).symm
  have hrel := congrArg Subtype.val hz'
  rw [frameTorsionHom_val] at hrel
  exact Level.Cover.LevelCover.frame_relations_nonzero A N U (j ≫ f) c.toAdd
    (fun h => hne (Multiplicative.toAdd.injective h)) hrel

def frameChangeEquiv [NeZero N] (α : A.FullLevel N) (T : Over S)
    (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (t : T.left) : Coefficients g N ≃* Coefficients g N :=
  MulEquiv.ofBijective (frameChangeAt A α T f t)
    ((Finite.injective_iff_bijective).mp (frameChangeAt_injective A α T f t))

/-- The changes of basis vary locally constantly, including on
disconnected and nonreduced schemes. -/
def frameChangeLabels [NeZero N] (α : A.FullLevel N) (T : Over S)
    (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    LocallyConstant T.left (Coefficients g N ≃* Coefficients g N) where
  toFun := frameChangeEquiv A α T f
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    have h : ∀ᶠ u in 𝓝 t, ∀ c : Coefficients g N,
        frameChangeHom A α T f c u = frameChangeHom A α T f c t :=
      Filter.eventually_all.mpr (fun c =>
        (frameChangeHom A α T f c).isLocallyConstant.eventually_eq t)
    exact h.mono (fun _ hu => MulEquiv.ext hu)

/-- A map into the frame scheme constructs a full level on the actual
base-changed abelian scheme, using the proved invertible label change. -/
def fullLevelFromFrame [NeZero N] (α : A.FullLevel N) (T : Over S)
    (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) : (A.pullback T.hom).FullLevel N :=
  HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoOfLabels (frameChangeLabels A α T f) ≪≫ α.pullback T.hom

def identityTestOver (T : Over S) : Over S :=
  (Over.map T.hom).obj (Over.mk (𝟙 T.left))

def identityTestTo (T : Over S) : identityTestOver T ⟶ T :=
  Over.homMk (𝟙 T.left) (by simp [identityTestOver])

/-- Reconstructed full levels send every constant coefficient vector to
the section defined by the original frame, after the actual pullback
identification. This is a compatibility theorem, not constructor data. -/
theorem fullLevelFromFrame_coefficients [NeZero N] (α : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (c : Coefficients g N) :
    A.torsionBaseChangeEquiv T.hom (Over.mk (𝟙 T.left)) N
      ((fullLevelFromFrame A α T f).hom.app (.op (Over.mk (𝟙 T.left)))
        (LocallyConstant.const T.left c)) =
      A.torsionPullback N (identityTestTo T) (frameTorsionHom A T f c) := by
  let e := A.torsionBaseChangeEquiv T.hom (Over.mk (𝟙 T.left)) N
  let β := HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoOfLabels (frameChangeLabels A α T f)
  have hlabels : β.hom.app (.op (Over.mk (𝟙 T.left))) (LocallyConstant.const T.left c) =
      frameChangeHom A α T f c := by
    apply LocallyConstant.ext
    intro x
    rfl
  change e (e.symm (α.hom.app (.op (identityTestOver T))
    (β.hom.app (.op (Over.mk (𝟙 T.left))) (LocallyConstant.const T.left c)))) = _
  refine (e.apply_symm_apply _).trans ?_
  refine (congrArg (fun d => α.hom.app (.op (identityTestOver T)) d) hlabels).trans ?_
  have hn := ConcreteCategory.congr_hom (α.hom.naturality (identityTestTo T).op)
    (frameChangeHom A α T f c)
  have hid : (frameChangeHom A α T f c).comap
      ⟨(identityTestTo T).left, (identityTestTo T).left.continuous⟩ =
        frameChangeHom A α T f c := by ext x; rfl
  change α.hom.app (.op (identityTestOver T))
      ((frameChangeHom A α T f c).comap
        ⟨(identityTestTo T).left, (identityTestTo T).left.continuous⟩) =
    A.torsionPullback N (identityTestTo T)
      (α.hom.app (.op T) (frameChangeHom A α T f c)) at hn
  rw [hid] at hn
  have hcancel : α.hom.app (.op T) (frameChangeHom A α T f c) = frameTorsionHom A T f c :=
    (α.app (.op T)).groupIsoToMulEquiv.apply_symm_apply _
  exact hn.trans (congrArg (A.torsionPullback N (identityTestTo T)) hcancel)

/-- In particular the finite etale frame scheme has its constructed
universal full level whenever the torsion is trivialized on the base. -/
def universalSplitFrameLevel [NeZero N] (α : A.FullLevel N) :
    (A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).FullLevel N :=
  fullLevelFromFrame A α (Level.Cover.LevelCover.frameScheme A N) (𝟙 _)

/-- A full-level isomorphism is determined by its constant sections on
the base. Naturality and locally constant decomposition handle all tests. -/
theorem fullLevel_ext_on_constants (α β : A.FullLevel N)
    (h : ∀ c : Coefficients g N,
      α.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c) =
        β.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c)) : α = β := by
  apply (Level.Data.framesEquivAut α).injective
  apply Iso.ext
  apply HilbertConstruction.Constant.GroupMaps.constantGroupMap_ext
  intro s
  apply MonoidHom.ext
  intro c
  change LocallyConstant.toFun
      (α.inv.app (.op (Over.mk (𝟙 S)))
        (α.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c))) s =
    LocallyConstant.toFun
      (α.inv.app (.op (Over.mk (𝟙 S)))
        (β.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c))) s
  exact congrArg (fun v => LocallyConstant.toFun (α.inv.app (.op (Over.mk (𝟙 S))) v) s) (h c)

/-- Reconstruction is independent of the initially chosen trivialization.
This compatibility is needed when the split constructions are descended. -/
theorem fullLevelFromFrame_independent [NeZero N] (α β : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    fullLevelFromFrame A α T f = fullLevelFromFrame A β T f := by
  apply fullLevel_ext_on_constants
  intro c
  apply (A.torsionBaseChangeEquiv T.hom (Over.mk (𝟙 T.left)) N).injective
  exact (fullLevelFromFrame_coefficients A α T f c).trans
    (fullLevelFromFrame_coefficients A β T f c).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover
