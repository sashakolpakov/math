import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentedGroupCoordinateTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.GroupBoundsCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DataEmbeddingRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.ForgetMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PullbackParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSectionExt
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeTransport

/-! # Level Reembedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelReembedding.NativeHilbertFullLevelReembedding

noncomputable section

/-! Reembedding an actual bounded projective abelian family in a native
Hilbert fiber gives an original full-level Hilbert classifier. The
classifier recovers the original group, every level label, and the
specified projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem inv_comp_of_hom_comp {C : Type*} [Category* C]
    {X Y Z : C} (e : X ≅ Y) (a : Y ⟶ Z) (b : X ⟶ Z) (h : e.hom ≫ a = b) :
    e.inv ≫ b = a :=
  (congrArg (fun f => e.inv ≫ f) h.symm).trans (e.inv_hom_id_assoc a)

private theorem recovered_triangle {C : Type*} [Category* C] {V W X Y : C}
    (r : V ⟶ W) (a : V ⟶ X) (q : X ⟶ W) (j : W ⟶ Y) (k : X ⟶ Y)
    (hr : r = a ≫ q) (hq : q ≫ j = k) : r ≫ j = a ≫ k :=
  (congrArg (fun f => f ≫ j) hr).trans
    ((Category.assoc _ _ _).trans (congrArg (fun f => a ≫ f) hq))

private theorem reassociate_five {C : Type*} [Category* C] {V W X Y Z U : C}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (d : Y ⟶ Z) (e : Z ⟶ U) :
    a ≫ b ≫ c ≫ d ≫ e = (a ≫ b ≫ c) ≫ d ≫ e := by
  simp only [Category.assoc]

private theorem postcompose_two_of_eq {C : Type*} [Category* C] {V W X Y Z : C}
    (a : V ⟶ W) (f : W ⟶ X) (c : V ⟶ X) (d : X ⟶ Y) (e : Y ⟶ Z)
    (k : W ⟶ Z) (hk : k = f ≫ d ≫ e) (h : a ≫ f = c) : a ≫ k = c ≫ d ≫ e :=
  (congrArg (fun j => a ≫ j) hk).trans
    ((Category.assoc a f (d ≫ e)).symm.trans
      (congrArg (fun j => j ≫ d ≫ e) h))

private theorem marked_triangle {C : Type*} [Category* C] {V W X Y : C}
    (a : V ⟶ W) (b : V ⟶ X) (r : W ⟶ X) (j : X ⟶ Y) (k : W ⟶ Y)
    (hb : b = a ≫ r) (hr : r ≫ j = k) : b ≫ j = a ≫ k :=
  (congrArg (fun f => f ≫ j) hb).trans
    ((Category.assoc _ _ _).trans (congrArg (fun f => a ≫ f) hr))

section LevelTransport
variable {B₀ : Scheme.{u}} {g N : ℕ} {A B C : Abelian.Schemes.AbelianScheme g B₀}
    (a : A.scheme ≅ B.scheme) (q : C.scheme ≅ B.scheme)
    [IsMonHom a.hom] [IsMonHom q.hom]

local instance inverseLevelMap_isMonHom : IsMonHom q.symm.hom :=
  inferInstanceAs (IsMonHom q.inv)

local instance recoveredLevelMap_isMonHom : IsMonHom (a ≪≫ q.symm).hom :=
  inferInstanceAs (IsMonHom (a.hom ≫ q.inv))

private theorem transport_comp_inverse (l : A.FullLevel N) (k : C.FullLevel N)
    (h : k.transport q = l.transport a) : l.transport (a ≪≫ q.symm) = k :=
  (Abelian.Schemes.AbelianScheme.FullLevel.transport_trans a q.symm l).symm.trans
    ((congrArg (fun v : B.FullLevel N => v.transport q.symm) h.symm).trans
      (Abelian.Schemes.AbelianScheme.FullLevel.transport_symm q k))
end LevelTransport

local instance reembeddingPullbackFlat {S T : Scheme.{u}}
    (f : T ⟶ S) (X : Over S) [Flat X.hom] : Flat ((Over.pullback f).obj X).hom :=
  inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd X.hom f))
local instance reembeddingPullbackFinitePresentation {S T : Scheme.{u}}
    (f : T ⟶ S) (X : Over S) [LocallyOfFinitePresentation X.hom] :
    LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd X.hom f))
local instance reembeddingPullbackSeparated {S T : Scheme.{u}}
    (f : T ⟶ S) (X : Over S) [IsSeparated X.hom] : IsSeparated ((Over.pullback f).obj X).hom :=
  inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd X.hom f))

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ)
    (g : ℕ) (Hm Hi : Polynomial ℚ) {T : Over S}

private theorem abelianDataInverse_embedding_left
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n H g Hm Hi T) :
    (Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n H g Hm Hi D).inv.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange
        ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n H g Hm Hi T).symm D).left).embedding.left =
      (D.val.projective S n H g Hm Hi).embedding.left := by
  let B : Abelian.Schemes.AbelianScheme g T.left := D.abelianScheme S n H g Hm Hi
  let U : Abelian.Schemes.AbelianScheme g T.left :=
    (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n H g Hm Hi T).symm D).left
  let q : U.scheme ≅ B.scheme := Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n H g Hm Hi D
  let a : B.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    (D.val.projective S n H g Hm Hi).embedding.left
  let b : U.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n H g Hm Hi T).symm D).left).embedding.left
  have h : q.hom.left ≫ a = b :=
    congrArg Over.Hom.left (Fixed.DataEmbeddingRecovery.fixedDimensionHilbertAbelianDataFamilyIso_embedding S n H g Hm Hi D)
  exact inv_comp_of_hom_comp ((Over.forget T.left).mapIso q) a b h

private theorem fullLevelDataInverse_embedding_left (N : ℕ) [NeZero N]
    (D : Fixed.LevelDataRecovery.FixedDimensionHilbertFullLevelData S n H g Hm Hi N T) :
    (Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n H g Hm Hi N D).inv.left ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n H g Hm Hi N T).symm D).left).embedding.left =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange D.1.left).embedding.left := by
  let B : Abelian.Schemes.AbelianScheme g T.left := (D.family S n H g Hm Hi N).abelian
  let U : Abelian.Schemes.AbelianScheme g T.left :=
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n H g Hm Hi N T).symm D).left
  let q : U.scheme ≅ B.scheme := Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n H g Hm Hi N D
  let a : B.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange D.1.left).embedding.left
  let b : U.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n H g Hm Hi N T).symm D).left).embedding.left
  have h : q.hom.left ≫ a = b :=
    congrArg Over.Hom.left (Fixed.DataEmbeddingRecovery.fixedDimensionHilbertFullLevelDataFamilyIso_embedding S n H g Hm Hi N D)
  exact inv_comp_of_hom_comp ((Over.forget T.left).mapIso q) a b h

private theorem forget_eq_fixedHilbert (N : ℕ) [NeZero N] :
    HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S n H g Hm Hi N =
      HilbertLevel.ForgetMaps.fixedDimensionHilbertFullLevelHilbertMap S n H g Hm Hi N ≫
        FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n H g ≫ SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n H :=
  reassociate_five (HilbertLevel.ForgetMaps.fixedDimensionHilbertFullLevelAbelianMap S n H g Hm Hi N)
    (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n H g Hm Hi)
    (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupHilbertMap S n H g Hm Hi)
    (FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n H g) (SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n H)

variable (A : Abelian.Schemes.AbelianScheme g T.left) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (c : T ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter S n H g)
    (e : A.scheme ≅ (Over.pullback c.left).obj (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).family.scheme)
    (eL : (((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left).ampleLineBundle.pullback
      e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ProjectiveGraphBounds P Hm Hi)

def operations : FamilyGroup.Operations.FamilyGroupOperations
    ((Over.pullback c.left).obj (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).family.scheme) :=
  (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ofIso e

omit [AlgebraicGeometry.IsNoetherian S] in
theorem operations_laws : (operations S n H g A c e).Laws :=
  (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ofIso_laws e
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj_laws A.scheme)

omit [AlgebraicGeometry.IsNoetherian S] in
include P eL hb in
theorem operations_bounds :
    (operations S n H g A c e).ProjectiveGraphBounds
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left) Hm Hi :=
  FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofBundleIso P
    ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left)
    e eL (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme) Hm Hi hb

def groupData : FixedDimension.GroupPointData.FixedDimensionHilbertGroupData S n H g Hm Hi T :=
  ⟨c, GroupBoundsCriterion.boundedNativeOperationsOfGraphBounds
    (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g) Hm Hi (Over.mk c.left)
    (operations S n H g A c e) (operations_laws S n H g A c e)
    (operations_bounds S n H g Hm Hi A P c e eL hb)⟩

def abelianData : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n H g Hm Hi T :=
  ⟨groupData S n H g Hm Hi A P c e eL hb, (A.transport e).connected⟩

def nativeIso : A.scheme ≅
    ((abelianData S n H g Hm Hi A P c e eL hb).abelianScheme S n H g Hm Hi).scheme := e

instance nativeIso_isMonHom : IsMonHom (nativeIso S n H g Hm Hi A P c e eL hb).hom :=
  isMonHom_ofIso e

def abelianClassifier : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n H g Hm Hi :=
  (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n H g Hm Hi T).symm
    (abelianData S n H g Hm Hi A P c e eL hb)

theorem abelianClassifier_data :
    FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n H g Hm Hi T
      (abelianClassifier S n H g Hm Hi A P c e eL hb) =
        abelianData S n H g Hm Hi A P c e eL hb :=
  Equiv.apply_symm_apply _ _

def abelianRecovery : A.scheme ≅
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback
      (abelianClassifier S n H g Hm Hi A P c e eL hb).left).scheme :=
  nativeIso S n H g Hm Hi A P c e eL hb ≪≫
    (Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n H g Hm Hi
      (abelianData S n H g Hm Hi A P c e eL hb)).symm

instance abelianRecovery_isMonHom : IsMonHom (abelianRecovery S n H g Hm Hi A P c e eL hb).hom := by
  let D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n H g Hm Hi T := abelianData S n H g Hm Hi A P c e eL hb
  let B : Abelian.Schemes.AbelianScheme g T.left := D.abelianScheme S n H g Hm Hi
  let U : Abelian.Schemes.AbelianScheme g T.left :=
    (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback
      (abelianClassifier S n H g Hm Hi A P c e eL hb).left
  let a : A.scheme ≅ B.scheme := nativeIso S n H g Hm Hi A P c e eL hb
  let q : U.scheme ≅ B.scheme := Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n H g Hm Hi D
  let : IsMonHom a.hom := nativeIso_isMonHom S n H g Hm Hi A P c e eL hb
  let : IsMonHom q.hom := Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso_isMonHom S n H g Hm Hi D
  exact inferInstanceAs (IsMonHom (a.hom ≫ q.inv))

private theorem abelianRecovery_hom_left :
    (abelianRecovery S n H g Hm Hi A P c e eL hb).hom.left =
      e.hom.left ≫ (Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n H g Hm Hi
        (abelianData S n H g Hm Hi A P c e eL hb)).inv.left := rfl

private theorem abelianRecovery_embedding_left :
    (abelianRecovery S n H g Hm Hi A P c e eL hb).hom.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange
        (abelianClassifier S n H g Hm Hi A P c e eL hb).left).embedding.left =
      e.hom.left ≫ ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left).embedding.left := by
  let D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n H g Hm Hi T := abelianData S n H g Hm Hi A P c e eL hb
  let B : Abelian.Schemes.AbelianScheme g T.left := D.abelianScheme S n H g Hm Hi
  let U : Abelian.Schemes.AbelianScheme g T.left :=
    (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback
      (abelianClassifier S n H g Hm Hi A P c e eL hb).left
  let q : U.scheme ≅ B.scheme := Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n H g Hm Hi D
  let r : A.scheme.left ⟶ U.scheme.left := (abelianRecovery S n H g Hm Hi A P c e eL hb).hom.left
  let a : A.scheme.left ⟶ B.scheme.left := e.hom.left
  let j : U.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange
      (abelianClassifier S n H g Hm Hi A P c e eL hb).left).embedding.left
  let k : B.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    (D.val.projective S n H g Hm Hi).embedding.left
  have hr : r = a ≫ q.inv.left := abelianRecovery_hom_left S n H g Hm Hi A P c e eL hb
  have hq : q.inv.left ≫ j = k := abelianDataInverse_embedding_left S n H g Hm Hi D
  exact recovered_triangle r a q.inv.left j k hr hq

theorem abelianRecovery_embedding :
    (abelianRecovery S n H g Hm Hi A P c e eL hb).hom ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange
        (abelianClassifier S n H g Hm Hi A P c e eL hb).left).embedding =
      e.hom ≫ ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left).embedding := by
  apply Over.OverMorphism.ext
  exact abelianRecovery_embedding_left S n H g Hm Hi A P c e eL hb

variable (N : ℕ) [NeZero N] (level : A.FullLevel N)

def fullLevelData : Fixed.LevelDataRecovery.FixedDimensionHilbertFullLevelData S n H g Hm Hi N T :=
  ⟨abelianClassifier S n H g Hm Hi A P c e eL hb,
    level.transport (abelianRecovery S n H g Hm Hi A P c e eL hb)⟩

def classifier : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n H g Hm Hi N :=
  (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n H g Hm Hi N T).symm
    (fullLevelData S n H g Hm Hi A P c e eL hb N level)

theorem classifier_data :
    FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n H g Hm Hi N T
      (classifier S n H g Hm Hi A P c e eL hb N level) =
        fullLevelData S n H g Hm Hi A P c e eL hb N level := Equiv.apply_symm_apply _ _

theorem classifier_toFixedHilbert :
    classifier S n H g Hm Hi A P c e eL hb N level ≫
      HilbertLevel.ForgetMaps.fixedDimensionHilbertFullLevelHilbertMap S n H g Hm Hi N = c := by
  have hF := congrArg Sigma.fst (classifier_data S n H g Hm Hi A P c e eL hb N level)
  rw [HilbertLevel.ForgetMaps.fixedDimensionHilbertFullLevelPoint_abelian] at hF
  have hA := congrArg
    (fun D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n H g Hm Hi T => D.val.1)
    (abelianClassifier_data S n H g Hm Hi A P c e eL hb)
  rw [HilbertLevel.ForgetMaps.fixedDimensionHilbertAbelianNativePoint_hilbert] at hA
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, hF]
  exact hA

theorem classifier_forget :
    classifier S n H g Hm Hi A P c e eL hb N level ≫
      HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S n H g Hm Hi N =
        c ≫ FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n H g ≫ SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n H := by
  exact postcompose_two_of_eq
    (classifier S n H g Hm Hi A P c e eL hb N level)
    (HilbertLevel.ForgetMaps.fixedDimensionHilbertFullLevelHilbertMap S n H g Hm Hi N) c
    (FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n H g) (SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n H)
    (HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S n H g Hm Hi N)
    (forget_eq_fixedHilbert S n H g Hm Hi N)
    (classifier_toFixedHilbert S n H g Hm Hi A P c e eL hb N level)

def recovery : A.scheme ≅
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback
      (classifier S n H g Hm Hi A P c e eL hb N level).left).scheme :=
  abelianRecovery S n H g Hm Hi A P c e eL hb ≪≫
    (Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n H g Hm Hi N
      (fullLevelData S n H g Hm Hi A P c e eL hb N level)).symm

instance recovery_isMonHom : IsMonHom (recovery S n H g Hm Hi A P c e eL hb N level).hom := by
  let D : Fixed.LevelDataRecovery.FixedDimensionHilbertFullLevelData S n H g Hm Hi N T :=
    fullLevelData S n H g Hm Hi A P c e eL hb N level
  let B : Abelian.Schemes.AbelianScheme g T.left := (D.family S n H g Hm Hi N).abelian
  let U : Abelian.Schemes.AbelianScheme g T.left :=
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback
      (classifier S n H g Hm Hi A P c e eL hb N level).left
  let a : A.scheme ≅ B.scheme := abelianRecovery S n H g Hm Hi A P c e eL hb
  let q : U.scheme ≅ B.scheme := Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n H g Hm Hi N D
  let : IsMonHom a.hom := abelianRecovery_isMonHom S n H g Hm Hi A P c e eL hb
  let : IsMonHom q.hom := Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso_isMonHom S n H g Hm Hi N D
  exact inferInstanceAs (IsMonHom (a.hom ≫ q.inv))

theorem recovery_level :
    level.transport (recovery S n H g Hm Hi A P c e eL hb N level) =
      (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n H g Hm Hi N).pullback
        (classifier S n H g Hm Hi A P c e eL hb N level).left := by
  let D : Fixed.LevelDataRecovery.FixedDimensionHilbertFullLevelData S n H g Hm Hi N T :=
    fullLevelData S n H g Hm Hi A P c e eL hb N level
  let B : Abelian.Schemes.AbelianScheme g T.left := (D.family S n H g Hm Hi N).abelian
  let U : Abelian.Schemes.AbelianScheme g T.left :=
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback
      (classifier S n H g Hm Hi A P c e eL hb N level).left
  let a : A.scheme ≅ B.scheme := abelianRecovery S n H g Hm Hi A P c e eL hb
  let q : U.scheme ≅ B.scheme := Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n H g Hm Hi N D
  let k : U.FullLevel N := (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n H g Hm Hi N).pullback
    (classifier S n H g Hm Hi A P c e eL hb N level).left
  let : IsMonHom a.hom := abelianRecovery_isMonHom S n H g Hm Hi A P c e eL hb
  let : IsMonHom q.hom := Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso_isMonHom S n H g Hm Hi N D
  have hq : k.transport q = level.transport a :=
    Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso_level S n H g Hm Hi N D
  exact transport_comp_inverse (A := A) (B := B) (C := U) a q level k hq

private theorem recovery_hom_left :
    (recovery S n H g Hm Hi A P c e eL hb N level).hom.left =
      (abelianRecovery S n H g Hm Hi A P c e eL hb).hom.left ≫
        (Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n H g Hm Hi N
          (fullLevelData S n H g Hm Hi A P c e eL hb N level)).inv.left := rfl

theorem recovery_embedding_left :
    (recovery S n H g Hm Hi A P c e eL hb N level).hom.left ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
        (classifier S n H g Hm Hi A P c e eL hb N level).left).embedding.left =
      e.hom.left ≫ ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left).embedding.left := by
  let D : Fixed.LevelDataRecovery.FixedDimensionHilbertFullLevelData S n H g Hm Hi N T :=
    fullLevelData S n H g Hm Hi A P c e eL hb N level
  let B : Abelian.Schemes.AbelianScheme g T.left := (D.family S n H g Hm Hi N).abelian
  let U : Abelian.Schemes.AbelianScheme g T.left :=
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback
      (classifier S n H g Hm Hi A P c e eL hb N level).left
  let q : U.scheme ≅ B.scheme := Fixed.LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n H g Hm Hi N D
  let r : A.scheme.left ⟶ U.scheme.left := (recovery S n H g Hm Hi A P c e eL hb N level).hom.left
  let a : A.scheme.left ⟶ B.scheme.left := (abelianRecovery S n H g Hm Hi A P c e eL hb).hom.left
  let j : U.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
      (classifier S n H g Hm Hi A P c e eL hb N level).left).embedding.left
  let k : B.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange D.1.left).embedding.left
  let i : A.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    e.hom.left ≫ ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left).embedding.left
  have hr : r = a ≫ q.inv.left := recovery_hom_left S n H g Hm Hi A P c e eL hb N level
  have hq : q.inv.left ≫ j = k := fullLevelDataInverse_embedding_left S n H g Hm Hi N D
  have ha : a ≫ k = i := abelianRecovery_embedding_left S n H g Hm Hi A P c e eL hb
  exact (recovered_triangle r a q.inv.left j k hr hq).trans ha

theorem recovery_embedding :
    (recovery S n H g Hm Hi A P c e eL hb N level).hom ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
        (classifier S n H g Hm Hi A P c e eL hb N level).left).embedding =
      e.hom ≫ ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left).embedding := by
  apply Over.OverMorphism.ext
  exact recovery_embedding_left S n H g Hm Hi A P c e eL hb N level

theorem recovery_markedSection (label : Multiplicative (Fin (2 * g) → ZMod N)) :
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback
        (classifier S n H g Hm Hi A P c e eL hb N level).left).fullLevelGlobalSection
      ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n H g Hm Hi N).pullback
        (classifier S n H g Hm Hi A P c e eL hb N level).left) label ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
        (classifier S n H g Hm Hi A P c e eL hb N level).left).embedding.left =
      A.fullLevelGlobalSection level label ≫ e.hom.left ≫
        ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left).embedding.left := by
  let U : Abelian.Schemes.AbelianScheme g T.left :=
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback
      (classifier S n H g Hm Hi A P c e eL hb N level).left
  let l : U.FullLevel N := (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n H g Hm Hi N).pullback
    (classifier S n H g Hm Hi A P c e eL hb N level).left
  let r : A.scheme.left ⟶ U.scheme.left := (recovery S n H g Hm Hi A P c e eL hb N level).hom.left
  let a : T.left ⟶ A.scheme.left := A.fullLevelGlobalSection level label
  let b : T.left ⟶ U.scheme.left := U.fullLevelGlobalSection l label
  let j : U.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
      (classifier S n H g Hm Hi A P c e eL hb N level).left).embedding.left
  let k : A.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    e.hom.left ≫ ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange c.left).embedding.left
  have hlevel : level.transport (recovery S n H g Hm Hi A P c e eL hb N level) = l :=
    recovery_level S n H g Hm Hi A P c e eL hb N level
  have htransport :
      U.fullLevelGlobalSection (level.transport (recovery S n H g Hm Hi A P c e eL hb N level)) label = a ≫ r :=
    Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_transport (B := U) level
      (recovery S n H g Hm Hi A P c e eL hb N level) label
  have ht : b = a ≫ r :=
    (congrArg (fun v : U.FullLevel N => U.fullLevelGlobalSection v label) hlevel).symm.trans htransport
  have hj : r ≫ j = k := recovery_embedding_left S n H g Hm Hi A P c e eL hb N level
  exact marked_triangle a b r j k ht hj

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelReembedding.NativeHilbertFullLevelReembedding
