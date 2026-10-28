import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Classification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterMapNaturality

/-! # Classifier Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ClassifierNaturality

noncomputable section

/-! The native recovery of the original Hilbert family commutes with
arbitrary changes of the test scheme. All equations concern the original
family projections and the original projective closed immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem square_of_ambient_triangles
    {C : Type*} [Category* C] {A A' B B' P P' Q Q' : C}
    (r : A ⟶ B) (r' : A' ⟶ B') (f : A' ⟶ A) (g : B' ⟶ B)
    (j : B ⟶ P) (j' : B' ⟶ P') (p : P' ⟶ P)
    (i : P ⟶ Q) (i' : P' ⟶ Q') (q : Q' ⟶ Q)
    (a : A ⟶ Q) (a' : A' ⟶ Q') [Mono j] [hiMono : Mono i]
    (hj : g ≫ j = j' ≫ p) (hi : p ≫ i = i' ≫ q)
    (hr : r ≫ j ≫ i = a) (hr' : r' ≫ j' ≫ i' = a')
    (ha : a' ≫ q = f ≫ a) : r' ≫ g = f ≫ r := by
  apply (cancel_mono j).mp
  apply (cancel_mono i).mp
  calc
    _ = r' ≫ ((g ≫ j) ≫ i) := by simp only [Category.assoc]
    _ = r' ≫ ((j' ≫ p) ≫ i) := congrArg (fun b => r' ≫ (b ≫ i)) hj
    _ = (r' ≫ j') ≫ (p ≫ i) := by simp only [Category.assoc]
    _ = (r' ≫ j') ≫ (i' ≫ q) := congrArg (fun b => (r' ≫ j') ≫ b) hi
    _ = (r' ≫ j' ≫ i') ≫ q := by simp only [Category.assoc]
    _ = a' ≫ q := congrArg (fun b => b ≫ q) hr'
    _ = f ≫ a := ha
    _ = _ := by rw [← hr]; simp only [Category.assoc]

variable {S : Scheme.{u}} (n : ℕ) (M : Over S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M)
    (P : Polynomial ℚ) (hP : HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    [IsLocallyNoetherian M.left]

/-- The recovery square before converting the native family to a
categorical pullback. -/
theorem nativeHilbertClassifierPullbackIso_projection
    {T : Over S} (a : T ⟶ M) :
    (Classification.nativeHilbertClassifierPullbackIso n M F P hP a).hom.left ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap
          (Over.homMk a.left rfl : Over.mk (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left ⟶ Over.mk ((Classification.nativeHilbertClassifier n M F P hP)).left) ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) =
      HilbertScheme.Presentations.Hilbert.Functor.familyMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F.val ≫ ((Classification.nativeHilbertClassifierIso n M F P hP)).hom.left := by
  let Q : Projective.ProjectivePresentations.ProjectivePresentation ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) :=
    ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion, inferInstance⟩
  let ca : Over.mk (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left ⟶ Over.mk ((Classification.nativeHilbertClassifier n M F P hP)).left := Over.homMk a.left rfl
  let r' := Classification.nativeHilbertClassifierPullbackIso n M F P hP a
  have hr : ((Classification.nativeHilbertClassifierIso n M F P hP)).hom.left ≫ (Q.baseChange ((Classification.nativeHilbertClassifier n M F P hP)).left).embedding.left ≫
      (ProjectiveAmbient.nativeHilbertAmbientIso M n).hom = F.val.subschemeι :=
    (Category.assoc _ _ _).symm.trans (Classification.nativeHilbertClassifierIso_ambient n M F P hP)
  have hr' : r'.hom.left ≫ (Q.baseChange (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left).embedding.left ≫
      (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom =
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F).val.subschemeι :=
    (Category.assoc _ _ _).symm.trans (Classification.nativeHilbertClassifierPullbackIso_ambient n M F P hP a)
  have hiMono : Mono (ProjectiveAmbient.nativeHilbertAmbientIso M n).hom :=
    @IsIso.mono_of_iso _ _ _ _ (ProjectiveAmbient.nativeHilbertAmbientIso M n).hom (ProjectiveAmbient.nativeHilbertAmbientIso M n).isIso_hom
  let : IsClosedImmersion (Q.baseChange ((Classification.nativeHilbertClassifier n M F P hP)).left).embedding.left :=
    (Q.baseChange ((Classification.nativeHilbertClassifier n M F P hP)).left).closedImmersion
  exact square_of_ambient_triangles (hiMono := hiMono)
    ((Classification.nativeHilbertClassifierIso n M F P hP)).hom.left r'.hom.left
    (HilbertScheme.Presentations.Hilbert.Functor.familyMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F.val) (Single.ParameterBaseChange.singleParameterBaseChangeMap ca ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme))
    (Q.baseChange ((Classification.nativeHilbertClassifier n M F P hP)).left).embedding.left (Q.baseChange (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left).embedding.left
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n)
    (ProjectiveAmbient.nativeHilbertAmbientIso M n).hom (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom
    (HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a) F.val.subschemeι (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F).val.subschemeι
    (Projective.ParameterMapNaturality.ProjectivePullback.parameterMap_embedding Q.embedding ca)
    (ProjectiveAmbient.nativeHilbertAmbientIso_natural a n) hr hr'
    (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F.val).w

/-- Compare the two ordinary categorical pullbacks, without changing
either family. -/
def nativeHilbertClassifierCartesianIso {T : Over S} (a : T ⟶ M) :
    (Over.pullback a.left).obj (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F) ≅
      (Over.pullback (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left).obj ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) :=
  (FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F).symm ≪≫ Classification.nativeHilbertClassifierPullbackIso n M F P hP a

theorem nativeHilbertClassifierCartesianIso_projection {T : Over S} (a : T ⟶ M) :
    (nativeHilbertClassifierCartesianIso n M F P hP a).hom.left ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap
          (Over.homMk a.left rfl : Over.mk (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left ⟶ Over.mk ((Classification.nativeHilbertClassifier n M F P hP)).left) ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) =
      pullback.fst (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F).hom a.left ≫ ((Classification.nativeHilbertClassifierIso n M F P hP)).hom.left := by
  change ((FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F).inv.left ≫
    (Classification.nativeHilbertClassifierPullbackIso n M F P hP a).hom.left) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F).inv.left ≫ q)
      (nativeHilbertClassifierPullbackIso_projection n M F P hP a)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ (Classification.nativeHilbertClassifierIso n M F P hP).hom.left)
          (FamilyPullbackPoints.nativeFamilyPullbackIso_inv_familyMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F))))

/-- The original Hilbert recovery is natural on every test scheme,
including non-Noetherian and nonreduced tests. -/
theorem nativeHilbertClassifierCartesianIso_natural
    {T U : Over S} (a : T ⟶ M) (u : U ⟶ T) :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u.left rfl : Over.mk (u ≫ a).left ⟶ Over.mk a.left)
        (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F) ≫
      (nativeHilbertClassifierCartesianIso n M F P hP a).hom.left =
    (nativeHilbertClassifierCartesianIso n M F P hP (u ≫ a)).hom.left ≫
      Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u.left (congrArg Over.Hom.left (Category.assoc u a (Classification.nativeHilbertClassifier n M F P hP)).symm) :
          Over.mk ((u ≫ a) ≫ (Classification.nativeHilbertClassifier n M F P hP)).left ⟶ Over.mk (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left) ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) := by
  let ca : Over.mk (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left ⟶ Over.mk ((Classification.nativeHilbertClassifier n M F P hP)).left := Over.homMk a.left rfl
  let cua : Over.mk ((u ≫ a) ≫ (Classification.nativeHilbertClassifier n M F P hP)).left ⟶ Over.mk ((Classification.nativeHilbertClassifier n M F P hP)).left := Over.homMk (u ≫ a).left rfl
  let cu : Over.mk ((u ≫ a) ≫ (Classification.nativeHilbertClassifier n M F P hP)).left ⟶ Over.mk (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left :=
    Over.homMk u.left (congrArg Over.Hom.left (Category.assoc u a (Classification.nativeHilbertClassifier n M F P hP)).symm)
  let ua : Over.mk (u ≫ a).left ⟶ Over.mk a.left := Over.homMk u.left rfl
  let e := nativeHilbertClassifierCartesianIso n M F P hP a
  let e' := nativeHilbertClassifierCartesianIso n M F P hP (u ≫ a)
  have hcomp : Single.ParameterBaseChange.singleParameterBaseChangeMap cu ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap ca ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) =
      Single.ParameterBaseChange.singleParameterBaseChangeMap cua ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) := by
    have hc : cu ≫ ca = cua := by apply Over.OverMorphism.ext; rfl
    exact (Single.ParameterFunctoriality.singleParameterBaseChangeMap_composition cu ca ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)).symm.trans
      (congrArg (fun q => Single.ParameterBaseChange.singleParameterBaseChangeMap q ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)) hc)
  apply (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback ca ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)).hom_ext
  · change (Single.ParameterBaseChange.singleParameterBaseChangeMap ua (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F) ≫ e.hom.left) ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap ca ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) =
      (e'.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap cu ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)) ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap ca ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)
    calc
      _ = Single.ParameterBaseChange.singleParameterBaseChangeMap ua (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F) ≫
          (pullback.fst (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F).hom a.left ≫ ((Classification.nativeHilbertClassifierIso n M F P hP)).hom.left) :=
        (Category.assoc _ _ _).trans (congrArg (fun q =>
          Single.ParameterBaseChange.singleParameterBaseChangeMap ua (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F) ≫ q)
          (nativeHilbertClassifierCartesianIso_projection n M F P hP a))
      _ = pullback.fst (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F).hom (u ≫ a).left ≫ ((Classification.nativeHilbertClassifierIso n M F P hP)).hom.left :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫ (Classification.nativeHilbertClassifierIso n M F P hP).hom.left)
            (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp ua (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F)))
      _ = e'.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap cua ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme) :=
        (nativeHilbertClassifierCartesianIso_projection n M F P hP (u ≫ a)).symm
      _ = _ := (congrArg (fun q => e'.hom.left ≫ q) hcomp.symm).trans (Category.assoc _ _ _).symm
  · change (Single.ParameterBaseChange.singleParameterBaseChangeMap ua (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F) ≫ e.hom.left) ≫
        ((Over.pullback (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left).obj ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)).hom =
      (e'.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap cu ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)) ≫
        ((Over.pullback (a ≫ (Classification.nativeHilbertClassifier n M F P hP)).left).obj ((Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme)).hom
    calc
      _ = Single.ParameterBaseChange.singleParameterBaseChangeMap ua (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F) ≫
          ((Over.pullback a.left).obj (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F)).hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun q => Single.ParameterBaseChange.singleParameterBaseChangeMap ua (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F) ≫ q) e.hom.w)
      _ = ((Over.pullback (u ≫ a).left).obj (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F)).hom ≫ u.left :=
        Single.ParameterFunctoriality.singleParameterBaseChangeMap_over ua (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) M F)
      _ = (e'.hom.left ≫ ((Over.pullback ((u ≫ a) ≫ Classification.nativeHilbertClassifier n M F P hP).left).obj
          (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme).hom) ≫ u.left :=
        congrArg (fun q => q ≫ u.left) e'.hom.w.symm
      _ = e'.hom.left ≫ (((Over.pullback ((u ≫ a) ≫ Classification.nativeHilbertClassifier n M F P hP).left).obj
          (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme).hom ≫ u.left) := Category.assoc _ _ _
      _ = e'.hom.left ≫ (Single.ParameterBaseChange.singleParameterBaseChangeMap cu (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme ≫
          ((Over.pullback (a ≫ Classification.nativeHilbertClassifier n M F P hP).left).obj
            (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme).hom) :=
        congrArg (fun q => e'.hom.left ≫ q)
          (Single.ParameterFunctoriality.singleParameterBaseChangeMap_over cu (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme).symm
      _ = _ := (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ClassifierNaturality
