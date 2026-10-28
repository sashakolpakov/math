import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Presentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelReembedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedFamilyIntrinsicPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Classifier

/-! # Abelian Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AbelianLift.NativeHilbertAbelianLift

noncomputable section

/-! A native Hilbert fiber isomorphic to an actual abelian scheme has a
canonical lift to the original fixed-dimension Hilbert open. The lift
retains the exact projective embedding, so bounded group operations and
an ordered full level can then be classified without changing the family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private def composeRecoveryIsos {U : Scheme.{u}} {X₀ X₁ X₂ X₃ : Over U}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃) : X₀ ≅ X₃ :=
  e₀ ≪≫ e₁ ≪≫ e₂

private theorem composeRecoveryIsos_hom_left {U : Scheme.{u}} {X₀ X₁ X₂ X₃ : Over U}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃) :
    (composeRecoveryIsos e₀ e₁ e₂).hom.left = e₀.hom.left ≫ e₁.hom.left ≫ e₂.hom.left := rfl

private def pullbackComparisonIso {X Y Z W : Scheme.{u}}
    (a : X ⟶ Y) (i : Y ⟶ W) (e : X ⟶ Z) (j : Z ⟶ W)
    (h : a ≫ i = e ≫ j) (L : W.Modules) {M : X.Modules}
    (eL : (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback j).obj L) ≅ M) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback i).obj L) ≅ M :=
  (Scheme.Modules.pullbackComp a i).app L ≪≫
    (Scheme.Modules.pullbackCongr h).app L ≪≫
    (Scheme.Modules.pullbackComp e j).symm.app L ≪≫ eL

private theorem inverse_triangle {C : Type*} [Category* C]
    {X Y Z : C} (e : X ≅ Y) (a : Y ⟶ Z) (b : X ⟶ Z) (h : e.hom ≫ a = b) :
    e.inv ≫ b = a :=
  (congrArg (fun f => e.inv ≫ f) h.symm).trans (e.inv_hom_id_assoc a)

private theorem recovered_triangle {C : Type*} [Category* C] {V W X Y : C}
    (r : V ⟶ W) (a : V ⟶ X) (q : X ⟶ W) (j : W ⟶ Y) (k : X ⟶ Y)
    (hr : r = a ≫ q) (hq : q ≫ j = k) : r ≫ j = a ≫ k :=
  (congrArg (fun f => f ≫ j) hr).trans
    ((Category.assoc _ _ _).trans (congrArg (fun f => a ≫ f) hq))

private theorem recovered_three_triangle {C : Type*} [Category* C] {V W X Y Z : C}
    (r : V ⟶ Y) (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y)
    (j : Y ⟶ Z) (k : X ⟶ Z) (l : W ⟶ Z)
    (hr : r = a ≫ b ≫ c) (hc : c ≫ j = k) (hb : b ≫ k = l) : r ≫ j = a ≫ l :=
  recovered_triangle r a (b ≫ c) j l hr
    ((Category.assoc b c j).trans ((congrArg (fun f => b ≫ f) hc).trans hb))

private theorem composeRecoveryIsos_embedding_left
    {U : Scheme.{u}} {X₀ X₁ X₂ X₃ : Over U} {Z : Scheme.{u}}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃)
    (j : X₃.left ⟶ Z) (k : X₂.left ⟶ Z) (l : X₁.left ⟶ Z)
    (he₂ : e₂.hom.left ≫ j = k) (he₁ : e₁.hom.left ≫ k = l) :
    (composeRecoveryIsos e₀ e₁ e₂).hom.left ≫ j = e₀.hom.left ≫ l :=
  recovered_three_triangle (composeRecoveryIsos e₀ e₁ e₂).hom.left
    e₀.hom.left e₁.hom.left e₂.hom.left j k l
    (composeRecoveryIsos_hom_left e₀ e₁ e₂) he₂ he₁

private theorem relativeFamily_embedding_left
    {B U : Scheme.{u}} {n : ℕ} {H : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily B n H) (f : U ⟶ B) :
    let P : Projective.ProjectivePresentations.ProjectivePresentation F.family.scheme := ⟨n, F.family.inclusion, inferInstance⟩
    (F.family.projectiveBaseChangeSchemeIso f).hom.left ≫ (P.baseChange f).embedding.left =
      (F.pullback f).family.inclusion.left :=
  congrArg (fun a : (F.family.projectiveBaseChange f).scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver U n => a.left)
    (F.family.projectiveBaseChangeSchemeIso_embedding f)

private theorem relativeFamily_inverse_embedding_left
    {B U : Scheme.{u}} {n : ℕ} {H : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily B n H) (f : U ⟶ B) :
    let P : Projective.ProjectivePresentations.ProjectivePresentation F.family.scheme := ⟨n, F.family.inclusion, inferInstance⟩
    (F.family.projectiveBaseChangeSchemeIso f).inv.left ≫ (F.pullback f).family.inclusion.left =
      (P.baseChange f).embedding.left := by
  let P : Projective.ProjectivePresentations.ProjectivePresentation F.family.scheme := ⟨n, F.family.inclusion, inferInstance⟩
  let q : (F.pullback f).family.scheme ≅ (Over.pullback f).obj F.family.scheme :=
    F.family.projectiveBaseChangeSchemeIso f
  let a : ((Over.pullback f).obj F.family.scheme).left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver U n).left :=
    (P.baseChange f).embedding.left
  let b : (F.pullback f).family.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver U n).left :=
    (F.pullback f).family.inclusion.left
  have h : q.hom.left ≫ a = b := relativeFamily_embedding_left F f
  exact inverse_triangle ((Over.forget U).mapIso q) a b h

private def relativeFamilyEqIso
    {U : Scheme.{u}} {n : ℕ} {H : Polynomial ℚ}
    {F G : RelativeProjective.Families.RelativeProjectiveHilbertFamily U n H} (h : F = G) :
    F.family.scheme ≅ G.family.scheme :=
  eqToIso (congrArg (fun K : RelativeProjective.Families.RelativeProjectiveHilbertFamily U n H => K.family.scheme) h)

private theorem relativeFamily_eq_inclusion_left
    {U : Scheme.{u}} {n : ℕ} {H : Polynomial ℚ}
    {F G : RelativeProjective.Families.RelativeProjectiveHilbertFamily U n H} (h : F = G) :
    (relativeFamilyEqIso h).hom.left ≫ G.family.inclusion.left = F.family.inclusion.left :=
  congrArg (fun a : F.family.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver U n => a.left)
    (Projective.ClosedFamilyIntrinsicPullback.relativeHilbertFamily_eqSchemeIso_inclusion h)

variable (S : Scheme.{u}) (n : ℕ) (H : Polynomial ℚ) (g : ℕ)

theorem fixedFamily_pullback (T : Over S) (c : T ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter S n H g) :
    (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).pullback c.left =
      (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback
        (c ≫ FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n H g ≫
          SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n H).left := by
  let F := Hilbert.ParameterScheme.hilbertUniversalFamily S n H
  let a := SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n H
  let b := FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n H g
  have h₁ : (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).pullback c.left =
      (F.pullback a.left).pullback (c.left ≫ b.left) :=
    (F.pullback a.left).pullback_comp b.left c.left
  have h₂ : (F.pullback a.left).pullback (c.left ≫ b.left) =
      F.pullback ((c.left ≫ b.left) ≫ a.left) :=
    F.pullback_comp a.left (c.left ≫ b.left)
  exact h₁.trans (h₂.trans (congrArg F.pullback (Category.assoc _ _ _)))

variable {T : Over S} (A : Abelian.Schemes.AbelianScheme g T.left)
    (b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H)
    (e : A.scheme ≅ (Over.pullback b.left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.scheme)

def closedRecovery : A.scheme ≅ ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left).family.scheme :=
  e ≪≫ ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.projectiveBaseChangeSchemeIso b.left).symm

def fixedFamily : FixedDimension.Parameters.FixedDimensionRelativeProjectiveHilbertFamily T.left n H g :=
  ⟨(Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left,
    (A.transport (closedRecovery S n H g A b e)).smoothDimension⟩

def classifier : T ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter S n H g :=
  (FixedDimension.PointEquivalence.fixedDimensionHilbertParameterPointEquiv S T n H g).symm (fixedFamily S n H g A b e)

theorem classifier_classifies :
    (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).pullback (classifier S n H g A b e).left =
      (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left :=
  (FixedDimension.PointEquivalence.fixedDimensionHilbertUniversalFamily_point S T n H g (classifier S n H g A b e)).trans
    (congrArg Subtype.val ((FixedDimension.PointEquivalence.fixedDimensionHilbertParameterPointEquiv S T n H g).apply_symm_apply
      (fixedFamily S n H g A b e)))

theorem classifier_forget :
    classifier S n H g A b e ≫ FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n H g ≫
      SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n H = b := by
  let F := (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left
  let : SmoothOfRelativeDimension g F.family.scheme.hom :=
    (fixedFamily S n H g A b e).property
  let : Smooth F.family.scheme.hom := SmoothOfRelativeDimension.smooth g _
  have h := (fixedFamily_pullback S n H g T (classifier S n H g A b e)).symm.trans
    (classifier_classifies S n H g A b e)
  exact (SmoothHilbert.Classifier.smoothHilbertClassifier_unique F _ h).trans (SmoothHilbert.Classifier.smoothHilbertClassifier_unique F b rfl).symm

private def recoveryComparison :
    ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left).family.scheme ≅
      ((FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).pullback
        (classifier S n H g A b e).left).family.scheme :=
  relativeFamilyEqIso (classifier_classifies S n H g A b e).symm

private def recoveryBaseChange :
    ((FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).pullback
      (classifier S n H g A b e).left).family.scheme ≅
      (Over.pullback (classifier S n H g A b e).left).obj
        (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).family.scheme :=
  (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).family.projectiveBaseChangeSchemeIso
    (classifier S n H g A b e).left

private theorem recoveryComparison_inclusion_left :
    (recoveryComparison S n H g A b e).hom.left ≫
      ((FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).pullback
        (classifier S n H g A b e).left).family.inclusion.left =
      ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left).family.inclusion.left :=
  relativeFamily_eq_inclusion_left (classifier_classifies S n H g A b e).symm

private theorem recoveryBaseChange_embedding_left :
    (recoveryBaseChange S n H g A b e).hom.left ≫
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange
        (classifier S n H g A b e).left).embedding.left =
      ((FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).pullback
        (classifier S n H g A b e).left).family.inclusion.left :=
  relativeFamily_embedding_left (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g)
    (classifier S n H g A b e).left

def recovery : A.scheme ≅
    (Over.pullback (classifier S n H g A b e).left).obj
      (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).family.scheme :=
  composeRecoveryIsos (closedRecovery S n H g A b e)
    (recoveryComparison S n H g A b e) (recoveryBaseChange S n H g A b e)

private theorem closedRecovery_hom_left :
    (closedRecovery S n H g A b e).hom.left = e.hom.left ≫
      ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.projectiveBaseChangeSchemeIso b.left).inv.left := rfl

private theorem closedRecovery_embedding_left :
    (closedRecovery S n H g A b e).hom.left ≫
      ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left).family.inclusion.left =
        e.hom.left ≫ ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left := by
  let F := Hilbert.ParameterScheme.hilbertUniversalFamily S n H
  let q : (F.pullback b.left).family.scheme ≅ (Over.pullback b.left).obj F.family.scheme :=
    F.family.projectiveBaseChangeSchemeIso b.left
  let r : A.scheme.left ⟶ (F.pullback b.left).family.scheme.left :=
    (closedRecovery S n H g A b e).hom.left
  let a : A.scheme.left ⟶ ((Over.pullback b.left).obj F.family.scheme).left := e.hom.left
  let j : (F.pullback b.left).family.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    (F.pullback b.left).family.inclusion.left
  let k : ((Over.pullback b.left).obj F.family.scheme).left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
    ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left
  have hr : r = a ≫ q.inv.left := closedRecovery_hom_left S n H g A b e
  have hq : q.inv.left ≫ j = k := relativeFamily_inverse_embedding_left F b.left
  exact recovered_triangle r a q.inv.left j k hr hq

theorem closedRecovery_embedding :
    (closedRecovery S n H g A b e).hom ≫
      ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left).family.inclusion =
        e.hom ≫ ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding := by
  apply Over.OverMorphism.ext
  exact closedRecovery_embedding_left S n H g A b e

private theorem recovery_hom_left :
    (recovery S n H g A b e).hom.left =
      (closedRecovery S n H g A b e).hom.left ≫
        (recoveryComparison S n H g A b e).hom.left ≫
        (recoveryBaseChange S n H g A b e).hom.left :=
  composeRecoveryIsos_hom_left (closedRecovery S n H g A b e)
    (recoveryComparison S n H g A b e) (recoveryBaseChange S n H g A b e)

private theorem recovery_closedEmbedding_left :
    (recovery S n H g A b e).hom.left ≫
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange
        (classifier S n H g A b e).left).embedding.left =
      (closedRecovery S n H g A b e).hom.left ≫
        ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left).family.inclusion.left :=
  composeRecoveryIsos_embedding_left (Z := (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left)
    (closedRecovery S n H g A b e)
    (recoveryComparison S n H g A b e) (recoveryBaseChange S n H g A b e)
    ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange
      (classifier S n H g A b e).left).embedding.left
    ((FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n H g).pullback
      (classifier S n H g A b e).left).family.inclusion.left
    ((Hilbert.ParameterScheme.hilbertUniversalFamily S n H).pullback b.left).family.inclusion.left
    (recoveryBaseChange_embedding_left S n H g A b e)
    (recoveryComparison_inclusion_left S n H g A b e)

theorem recovery_embedding_left :
    (recovery S n H g A b e).hom.left ≫
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange
        (classifier S n H g A b e).left).embedding.left =
      e.hom.left ≫ ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left :=
  (recovery_closedEmbedding_left S n H g A b e).trans
    (closedRecovery_embedding_left S n H g A b e)

theorem recovery_embedding :
    (recovery S n H g A b e).hom ≫
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange
        (classifier S n H g A b e).left).embedding =
      e.hom ≫ ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding := by
  apply Over.OverMorphism.ext
  exact recovery_embedding_left S n H g A b e

variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (eL : (((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).ampleLineBundle.pullback e.hom.left).sheaf ≅
      P.ampleLineBundle.sheaf)

def recoveryTwistingIso :
    (((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange
      (classifier S n H g A b e).left).ampleLineBundle.pullback
        (recovery S n H g A b e).hom.left).sheaf ≅ P.ampleLineBundle.sheaf := by
  let L := RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T.left n
  let a := (recovery S n H g A b e).hom.left
  let i := ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange
    (classifier S n H g A b e).left).embedding.left
  let j := ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left
  have h : a ≫ i = e.hom.left ≫ j := recovery_embedding_left S n H g A b e
  exact pullbackComparisonIso a i e.hom.left j h L.sheaf eL

variable [IsNoetherian S] (Hm Hi : Polynomial ℚ)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ProjectiveGraphBounds P Hm Hi)
    (N : ℕ) [NeZero N] (level : A.FullLevel N)

def fullLevelClassifier : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n H g Hm Hi N :=
  LevelReembedding.NativeHilbertFullLevelReembedding.classifier S n H g Hm Hi A P
    (classifier S n H g A b e) (recovery S n H g A b e)
    (recoveryTwistingIso S n H g A b e P eL) hb N level

theorem fullLevelClassifier_forget :
    fullLevelClassifier S n H g A b e P eL Hm Hi hb N level ≫
      HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S n H g Hm Hi N = b :=
  (LevelReembedding.NativeHilbertFullLevelReembedding.classifier_forget S n H g Hm Hi A P
    (classifier S n H g A b e) (recovery S n H g A b e)
    (recoveryTwistingIso S n H g A b e P eL) hb N level).trans
      (classifier_forget S n H g A b e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AbelianLift.NativeHilbertAbelianLift
