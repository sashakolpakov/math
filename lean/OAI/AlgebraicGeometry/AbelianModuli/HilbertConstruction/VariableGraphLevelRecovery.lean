import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelReembedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ClassifierIntrinsicRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.EmbeddedGroupGraphBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EmbeddingBundleRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementBaseChange

/-! # Variable Graph Level Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VariableGraphLevelRecovery.VariableGraphLevel

noncomputable section

/-! Every actual positive graph-power embedding, of any degree, has an
original full-level Hilbert classifier. Its native recovery preserves
the group, the ordered level, the embedding, and the graph-line power.
The test scheme is arbitrary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def rawNaturalTwistingIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (O : Z.Modules) (h : f ≫ j = i) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback j).obj O) ≅
      (Scheme.Modules.pullback i).obj O :=
  (Scheme.Modules.pullbackComp f j).app O ≪≫ (Scheme.Modules.pullbackCongr h).app O

private def fixedDimensionHilbertTwistingIso
    (B : Scheme.{u}) (n : ℕ) (H : Polynomial ℚ) (g : ℕ)
    {S : Scheme.{u}} {X : Over S}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion i.left]
    (c : S ⟶ (FixedDimension.Parameters.fixedDimensionHilbertParameter B n H g).left)
    (e : X ≅ (Over.pullback c).obj (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B n H g).family.scheme)
    (h : e.hom.left ≫ ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation B n H g).baseChange c).embedding.left = i.left) :
    ((((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation B n H g).baseChange c).ampleLineBundle).pullback
      e.hom.left).sheaf ≅ (⟨n, i, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation X).ampleLineBundle.sheaf := by
  let Q := (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation B n H g).baseChange c
  exact rawNaturalTwistingIso e.hom.left i.left Q.embedding.left
    (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf h

private def sourcePresentationHilbertTwistingIso
    (B : Scheme.{u}) (H : Polynomial ℚ) (g : ℕ)
    {S : Scheme.{u}} {X : Over S} (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (c : S ⟶ (FixedDimension.Parameters.fixedDimensionHilbertParameter B P.dimension H g).left)
    (e : X ≅ (Over.pullback c).obj (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B P.dimension H g).family.scheme)
    (h : e.hom.left ≫
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation B P.dimension H g).baseChange c).embedding.left = P.embedding.left) :
    ((((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation B P.dimension H g).baseChange c).ampleLineBundle).pullback
      e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf := by
  rcases P with ⟨n, i, hi⟩
  exact @fixedDimensionHilbertTwistingIso B n H g S X i hi c e h

private def recoveredSectionTwistingIso
    {B S : Scheme.{u}} {Y : Over B} {X : Over S}
    (P : Projective.ProjectivePresentations.ProjectivePresentation Y) (Q : Projective.ProjectivePresentations.ProjectivePresentation X)
    (L : Line.Bundles.LineBundle X.left) (D : Q.SectionData L)
    (c : S ⟶ B) (e : X ≅ (Over.pullback c).obj Y)
    (hn : P.dimension = Q.dimension)
    (h : HEq (e.hom.left ≫ (P.baseChange c).embedding.left) Q.embedding.left) :
    ((P.ampleLineBundle.pullback (pullback.fst Y.hom c)).pullback e.hom.left).sheaf ≅ L.sheaf := by
  rcases P with ⟨n, j, hj⟩
  rcases Q with ⟨m, i, hi⟩
  cases hn
  let P : Projective.ProjectivePresentations.ProjectivePresentation Y := ⟨n, j, hj⟩
  exact (Scheme.Modules.pullback e.hom.left).mapIso (P.baseChangeTwistingBundleIso c).symm ≪≫
    rawNaturalTwistingIso e.hom.left i.left (P.baseChange c).embedding.left
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf (eq_of_heq h) ≪≫ D.twistingIso

variable (B : Scheme.{u}) [IsNoetherian B] {S : Scheme.{u}}
    {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) (b : S ⟶ B)

def familyPolynomial : Polynomial ℚ :=
  (Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)

def additionPolynomial : Polynomial ℚ :=
  (AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ).comp (Polynomial.C (E.degree : ℚ) * Polynomial.X)

def inversionPolynomial : Polynomial ℚ :=
  (Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C ((E.degree * 2 : ℕ) : ℚ) * Polynomial.X)

def parameter : Over B :=
  FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) N

def universalFamily : Level.Data.AbelianSchemeWithFullLevel g N (parameter B A E).left :=
  FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) N

def projective : Projective.ProjectivePresentations.ProjectivePresentation (universalFamily B A E).abelian.scheme :=
  FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) N

def quasiProjective : Projective.ProjectivePresentations.QuasiProjectivePresentation (parameter B A E) :=
  FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelQuasiProjectivePresentation B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) N

instance parameter_noetherian : IsNoetherian (parameter B A E).left :=
  (quasiProjective B A E).noetherian

def hilbertPoint : Over.mk b ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter B E.dimension (familyPolynomial A E) g :=
  A.graphPowerEmbeddingHilbertClassifier hg hN hunit E b

def hilbertIso : A.abelian.scheme ≅
    (Over.pullback (hilbertPoint B A hg hN hunit E b).left).obj
      (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily B E.dimension (familyPolynomial A E) g).family.scheme :=
  A.graphPowerEmbeddingHilbertClassifier_nativeFamilyIso hg hN hunit E b

def hilbertTwistingIso :
    (((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation B E.dimension (familyPolynomial A E) g).baseChange
      (hilbertPoint B A hg hN hunit E b).left).ampleLineBundle.pullback
        (hilbertIso B A hg hN hunit E b).hom.left).sheaf ≅ E.projectivePresentation.ampleLineBundle.sheaf := by
  exact sourcePresentationHilbertTwistingIso B (familyPolynomial A E) g E.projectivePresentation
    (hilbertPoint B A hg hN hunit E b).left (hilbertIso B A hg hN hunit E b)
    (by convert (congrArg Over.Hom.left
      (A.graphPowerEmbeddingHilbertClassifier_nativeFamilyIso_embedding hg hN hunit E b)) using 2 <;> rfl)

omit [NeZero N] in
include hg hN hunit in
theorem graphBounds : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.abelian.scheme).ProjectiveGraphBounds
    E.projectivePresentation (additionPolynomial A E) (inversionPolynomial A E) :=
  ⟨A.additionGraph_relativePowerEmbedding_hilbertPolynomial hg hN hunit E,
    A.inversionGraph_relativePowerEmbedding_hilbertPolynomial hg hN hunit E⟩

def point : Over.mk b ⟶ parameter B A E :=
  Intrinsic.LevelReembedding.NativeHilbertFullLevelReembedding.classifier (T := Over.mk b) B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) A.abelian E.projectivePresentation
    (hilbertPoint B A hg hN hunit E b) (hilbertIso B A hg hN hunit E b)
    (hilbertTwistingIso B A hg hN hunit E b) (graphBounds A hg hN hunit E) N A.level

def recovery : A.abelian.scheme ≅
    ((universalFamily B A E).pullback (point B A hg hN hunit E b).left).abelian.scheme :=
  Intrinsic.LevelReembedding.NativeHilbertFullLevelReembedding.recovery (T := Over.mk b) B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) A.abelian E.projectivePresentation
    (hilbertPoint B A hg hN hunit E b) (hilbertIso B A hg hN hunit E b)
    (hilbertTwistingIso B A hg hN hunit E b) (graphBounds A hg hN hunit E) N A.level

instance recovery_isMonHom : IsMonHom (recovery B A hg hN hunit E b).hom :=
  Intrinsic.LevelReembedding.NativeHilbertFullLevelReembedding.recovery_isMonHom (T := Over.mk b) B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) A.abelian E.projectivePresentation
    (hilbertPoint B A hg hN hunit E b) (hilbertIso B A hg hN hunit E b)
    (hilbertTwistingIso B A hg hN hunit E b) (graphBounds A hg hN hunit E) N A.level

theorem recovery_level : A.level.transport (recovery B A hg hN hunit E b) =
    (universalFamily B A E).level.pullback (point B A hg hN hunit E b).left :=
  Intrinsic.LevelReembedding.NativeHilbertFullLevelReembedding.recovery_level (T := Over.mk b) B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) A.abelian E.projectivePresentation
    (hilbertPoint B A hg hN hunit E b) (hilbertIso B A hg hN hunit E b)
    (hilbertTwistingIso B A hg hN hunit E b) (graphBounds A hg hN hunit E) N A.level

theorem recovery_embedding_left :
    (recovery B A hg hN hunit E b).hom.left ≫
      ((projective B A E).baseChange (point B A hg hN hunit E b).left).embedding.left =
        E.projectivePresentation.embedding.left := by
  exact (Intrinsic.LevelReembedding.NativeHilbertFullLevelReembedding.recovery_embedding_left (T := Over.mk b) B E.dimension (familyPolynomial A E) g
    (additionPolynomial A E) (inversionPolynomial A E) A.abelian E.projectivePresentation
    (hilbertPoint B A hg hN hunit E b) (hilbertIso B A hg hN hunit E b)
    (hilbertTwistingIso B A hg hN hunit E b) (graphBounds A hg hN hunit E) N A.level).trans
      (by convert (congrArg Over.Hom.left
      (A.graphPowerEmbeddingHilbertClassifier_nativeFamilyIso_embedding hg hN hunit E b)) using 2 <;> rfl)

theorem recovery_embedding :
    (recovery B A hg hN hunit E b).hom ≫
      ((projective B A E).baseChange (point B A hg hN hunit E b).left).embedding =
        E.projectivePresentation.embedding := by
  apply Over.OverMorphism.ext
  exact recovery_embedding_left B A hg hN hunit E b

def recoveryGraphPowerIso :
    ((((projective B A E).ampleLineBundle).pullback
      (pullback.fst (universalFamily B A E).abelian.scheme.hom
        (point B A hg hN hunit E b).left)).pullback
          (recovery B A hg hN hunit E b).hom.left).sheaf ≅
            (A.graphBundle.tensorPower E.degree).sheaf := by
  exact recoveredSectionTwistingIso (projective B A E) E.projectivePresentation
    (A.graphBundle.tensorPower E.degree) E.canonicalPowerSectionData
    (point B A hg hN hunit E b).left (recovery B A hg hN hunit E b)
    rfl (heq_of_eq (recovery_embedding_left B A hg hN hunit E b))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VariableGraphLevelRecovery.VariableGraphLevel
