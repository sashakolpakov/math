import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ProjectiveFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterUniversality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedFamilyIntrinsicPullback

/-! # Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Classification

noncomputable section

/-! Actual native Hilbert classification on a Noetherian parameter, with
exact recovery over every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {S : Scheme.{u}}
variable (n : ℕ) (T : Over S) (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T)
variable (P : Polynomial ℚ) (hP : HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)

private def relativeProjectiveHilbertPullbackIso
    {U M : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P) (f : U ⟶ M) :
    (G.pullback f).family.scheme ≅ (Over.pullback f).obj G.family.scheme :=
  G.family.projectiveBaseChangeSchemeIso f

private theorem postcompose_inverse
    {C : Type*} [Category* C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ E) (e : E ≅ D)
    (h : a ≫ b = c ≫ e.hom) : a ≫ (b ≫ e.inv) = c := by
  rw [← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem compose_triangles
    {C : Type*} [Category* C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (j : E ⟶ F)
    (k : D ⟶ F) (l : B ⟶ F) (hc : c ≫ j = k) (hb : b ≫ k = l) :
    (a ≫ b ≫ c) ≫ j = a ≫ l := by
  calc
    (a ≫ b ≫ c) ≫ j = a ≫ (b ≫ (c ≫ j)) := by simp only [Category.assoc]
    _ = a ≫ (b ≫ k) := congrArg (fun h => a ≫ (b ≫ h)) hc
    _ = a ≫ l := congrArg (fun h => a ≫ h) hb

private theorem inverse_triangle
    {C : Type*} [Category* C] {A B D E : C}
    (e : A ≅ B) (j : A ⟶ D) (k : D ⟶ E) (l : B ⟶ E)
    (h : e.hom ≫ l = j ≫ k) : (e.inv ≫ j) ≫ k = l := by
  rw [Category.assoc, ← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

private theorem relativeProjectiveHilbertPullbackIso_embedding_left
    {U M : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P) (f : U ⟶ M) :
    (relativeProjectiveHilbertPullbackIso G f).hom.left ≫
      (((Over.pullback f).map G.family.inclusion).left ≫
        (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left) =
      (G.pullback f).family.inclusion.left := by
  exact congrArg Over.Hom.left (G.family.projectiveBaseChangeSchemeIso_embedding f)

private def relativeFamilyEqIso {U : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    {G H : RelativeProjective.Families.RelativeProjectiveHilbertFamily U n P} (h : G = H) :
    G.family.scheme ≅ H.family.scheme :=
  eqToIso (congrArg (fun F : RelativeProjective.Families.RelativeProjectiveHilbertFamily U n P => F.family.scheme) h)

private theorem relativeFamilyEqIso_inclusion_left
    {U : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    {G H : RelativeProjective.Families.RelativeProjectiveHilbertFamily U n P} (h : G = H) :
    (relativeFamilyEqIso h).hom.left ≫ H.family.inclusion.left = G.family.inclusion.left :=
  congrArg (fun a : G.family.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver U n => a.left)
    (Projective.ClosedFamilyIntrinsicPullback.relativeHilbertFamily_eqSchemeIso_inclusion h)

private def composeOverIsos {U : Scheme.{u}} {X₀ X₁ X₂ X₃ : Over U}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃) : X₀ ≅ X₃ :=
  e₀ ≪≫ e₁ ≪≫ e₂

private theorem composeOverIsos_hom_left {U : Scheme.{u}} {X₀ X₁ X₂ X₃ : Over U}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃) :
    (composeOverIsos e₀ e₁ e₂).hom.left = e₀.hom.left ≫ e₁.hom.left ≫ e₂.hom.left := rfl

private theorem composeOverIsos_triangle_left
    {U : Scheme.{u}} {X₀ X₁ X₂ X₃ : Over U} {Y : Scheme.{u}}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃)
    (j : X₃.left ⟶ Y) (k : X₂.left ⟶ Y) (l : X₁.left ⟶ Y)
    (hc : e₂.hom.left ≫ j = k) (hb : e₁.hom.left ≫ k = l) :
    (composeOverIsos e₀ e₁ e₂).hom.left ≫ j = e₀.hom.left ≫ l :=
  (congrArg (fun a : X₀.left ⟶ X₃.left => a ≫ j) (composeOverIsos_hom_left e₀ e₁ e₂)).trans
    (compose_triangles e₀.hom.left e₁.hom.left e₂.hom.left j k l hc hb)

private def relativeHilbertRecoveryIso
    {U M : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P) (H : RelativeProjective.Families.RelativeProjectiveHilbertFamily U n P)
    (f : U ⟶ M) (h : G.pullback f = H) {X : Over U} (e : X ≅ H.family.scheme) :
    X ≅ (Over.pullback f).obj G.family.scheme :=
  composeOverIsos e (relativeFamilyEqIso h.symm) (relativeProjectiveHilbertPullbackIso G f)

private theorem relativeHilbertRecoveryIso_embedding_left
    {U M : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P) (H : RelativeProjective.Families.RelativeProjectiveHilbertFamily U n P)
    (f : U ⟶ M) (h : G.pullback f = H) {X : Over U} (e : X ≅ H.family.scheme) :
    (relativeHilbertRecoveryIso G H f h e).hom.left ≫
      (((Over.pullback f).map G.family.inclusion).left ≫
        (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left) = e.hom.left ≫ H.family.inclusion.left := by
  cases h
  exact composeOverIsos_triangle_left e (Iso.refl _)
    (relativeProjectiveHilbertPullbackIso G f)
    (((Over.pullback f).map G.family.inclusion).left ≫
      (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left)
    (G.pullback f).family.inclusion.left (G.pullback f).family.inclusion.left
    (relativeProjectiveHilbertPullbackIso_embedding_left G f)
    (Category.id_comp _)

def nativeProjectiveHilbertRecoveryIso {M : Scheme.{u}} (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P)
    (f : T.left ⟶ M) (h : G.pullback f = ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP) :
    FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T F ≅ (Over.pullback f).obj G.family.scheme :=
  relativeHilbertRecoveryIso G (ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP) f h
    (ProjectiveFamily.nativeProjectiveClosedFamilyIso n T F).symm

private theorem nativeProjectiveHilbertRecoveryIso_embedding_left
    {M : Scheme.{u}} (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P)
    (f : T.left ⟶ M) (h : G.pullback f = ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP) :
    (nativeProjectiveHilbertRecoveryIso n T F P hP G f h).hom.left ≫
      (((Over.pullback f).map G.family.inclusion).left ≫
        (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left) =
      (ProjectiveFamily.nativeProjectiveClosedFamilyIso n T F).inv.left ≫
        (ProjectiveFamily.nativeProjectiveClosedFamily n T F).inclusion.left :=
  relativeHilbertRecoveryIso_embedding_left G (ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP)
    f h (ProjectiveFamily.nativeProjectiveClosedFamilyIso n T F).symm

theorem nativeProjectiveHilbertRecoveryIso_embedding
    {M : Scheme.{u}} (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P)
    (f : T.left ⟶ M) (h : G.pullback f = ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP) :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation G.family.scheme := ⟨n, G.family.inclusion, inferInstance⟩
    (nativeProjectiveHilbertRecoveryIso n T F P hP G f h).hom ≫ (Q.baseChange f).embedding =
      (ProjectiveFamily.nativeProjectiveClosedFamilyIso n T F).inv ≫ (ProjectiveFamily.nativeProjectiveClosedFamily n T F).inclusion := by
  apply Over.OverMorphism.ext
  exact nativeProjectiveHilbertRecoveryIso_embedding_left n T F P hP G f h

theorem nativeProjectiveHilbertRecoveryIso_ambient_left
    {M : Scheme.{u}} (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P)
    (f : T.left ⟶ M) (h : G.pullback f = ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP) :
    (nativeProjectiveHilbertRecoveryIso n T F P hP G f h).hom.left ≫
      (((Over.pullback f).map G.family.inclusion).left ≫
        (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left) ≫
          (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom = F.val.subschemeι := by
  have hleft := nativeProjectiveHilbertRecoveryIso_embedding_left n T F P hP G f h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a : (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T F).left ⟶
      (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left => a ≫ (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom) hleft).trans
      (inverse_triangle ((Over.forget T.left).mapIso (ProjectiveFamily.nativeProjectiveClosedFamilyIso n T F))
        (ProjectiveFamily.nativeProjectiveClosedFamily n T F).inclusion.left (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom
        F.val.subschemeι (ProjectiveFamily.nativeProjectiveClosedFamilyIso_embedding n T F)))

theorem nativeProjectiveHilbertRecoveryIso_ambient
    {M : Scheme.{u}} (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily M n P)
    (f : T.left ⟶ M) (h : G.pullback f = ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP) :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation G.family.scheme := ⟨n, G.family.inclusion, inferInstance⟩
    ((nativeProjectiveHilbertRecoveryIso n T F P hP G f h).hom ≫ (Q.baseChange f).embedding).left ≫
      (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom = F.val.subschemeι := by
  have hleft := nativeProjectiveHilbertRecoveryIso_embedding_left n T F P hP G f h
  exact (congrArg (fun a : (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T F).left ⟶
      (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left => a ≫ (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom) hleft).trans
    (inverse_triangle ((Over.forget T.left).mapIso (ProjectiveFamily.nativeProjectiveClosedFamilyIso n T F))
      (ProjectiveFamily.nativeProjectiveClosedFamily n T F).inclusion.left (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom
      F.val.subschemeι (ProjectiveFamily.nativeProjectiveClosedFamilyIso_embedding n T F))

variable [IsLocallyNoetherian T.left]

def nativeHilbertClassifier : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P :=
  Hilbert.ParameterEquivalence.hilbertParameterEquiv n P (ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP)

theorem nativeHilbertClassifier_classifies :
    (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback (nativeHilbertClassifier n T F P hP).left =
      ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP :=
  Hilbert.ParameterUniversality.hilbertUniversalFamily_classifies (ProjectiveFamily.nativeProjectiveHilbertFamily n T F P hP)

def nativeHilbertClassifierIso :
    FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T F ≅
      (Over.pullback (nativeHilbertClassifier n T F P hP).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
  nativeProjectiveHilbertRecoveryIso n T F P hP (Hilbert.ParameterScheme.hilbertUniversalFamily S n P)
    (nativeHilbertClassifier n T F P hP).left (nativeHilbertClassifier_classifies n T F P hP)

private theorem nativeHilbertClassifierIso_eq :
    nativeHilbertClassifierIso n T F P hP =
      nativeProjectiveHilbertRecoveryIso n T F P hP (Hilbert.ParameterScheme.hilbertUniversalFamily S n P)
        (nativeHilbertClassifier n T F P hP).left (nativeHilbertClassifier_classifies n T F P hP) := rfl

theorem nativeHilbertClassifierIso_ambient :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
      ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion, inferInstance⟩
    ((nativeHilbertClassifierIso n T F P hP).hom ≫
      (Q.baseChange (nativeHilbertClassifier n T F P hP).left).embedding).left ≫
        (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom = F.val.subschemeι := by
  rw [nativeHilbertClassifierIso_eq]
  exact nativeProjectiveHilbertRecoveryIso_ambient n T F P hP (Hilbert.ParameterScheme.hilbertUniversalFamily S n P)
    (nativeHilbertClassifier n T F P hP).left (nativeHilbertClassifier_classifies n T F P hP)

theorem nativeHilbertClassifier_pullback_classifies {U : Over S} (a : U ⟶ T) :
    (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback (a ≫ nativeHilbertClassifier n T F P hP).left =
      ProjectiveFamily.nativeProjectiveHilbertFamily n U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F)
        P (hP.pullback a) :=
  ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback_comp (nativeHilbertClassifier n T F P hP).left a.left).symm.trans
    ((congrArg (fun H : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P => H.pullback a.left)
      (nativeHilbertClassifier_classifies n T F P hP)).trans (ProjectiveFamily.nativeProjectiveHilbertFamily_pullback n F P hP a).symm)

def nativeHilbertClassifierPullbackIso {U : Over S} (a : U ⟶ T) :
    FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F) ≅
      (Over.pullback (a ≫ nativeHilbertClassifier n T F P hP).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
  nativeProjectiveHilbertRecoveryIso n U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F)
    P (hP.pullback a) (Hilbert.ParameterScheme.hilbertUniversalFamily S n P) (a ≫ nativeHilbertClassifier n T F P hP).left
    (nativeHilbertClassifier_pullback_classifies n T F P hP a)

private theorem nativeHilbertClassifierPullbackIso_eq {U : Over S} (a : U ⟶ T) :
    nativeHilbertClassifierPullbackIso n T F P hP a =
      nativeProjectiveHilbertRecoveryIso n U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F)
        P (hP.pullback a) (Hilbert.ParameterScheme.hilbertUniversalFamily S n P) (a ≫ nativeHilbertClassifier n T F P hP).left
        (nativeHilbertClassifier_pullback_classifies n T F P hP a) := rfl

theorem nativeHilbertClassifierPullbackIso_ambient {U : Over S} (a : U ⟶ T) :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
      ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion, inferInstance⟩
    ((nativeHilbertClassifierPullbackIso n T F P hP a).hom ≫
      (Q.baseChange (a ≫ nativeHilbertClassifier n T F P hP).left).embedding).left ≫
      (ProjectiveAmbient.nativeHilbertAmbientIso U n).hom = (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F).val.subschemeι := by
  rw [nativeHilbertClassifierPullbackIso_eq]
  exact nativeProjectiveHilbertRecoveryIso_ambient n U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F)
    P (hP.pullback a) (Hilbert.ParameterScheme.hilbertUniversalFamily S n P) (a ≫ nativeHilbertClassifier n T F P hP).left
    (nativeHilbertClassifier_pullback_classifies n T F P hP a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Classification
