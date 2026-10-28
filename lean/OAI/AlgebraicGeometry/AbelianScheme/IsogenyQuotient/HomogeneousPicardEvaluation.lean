import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedRelativePicardInjection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneous

/-! # Homogeneous Picard Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardEvaluation.Construction

noncomputable section

/-! A normalized homogeneous line-bundle family evaluates multiplicatively
on points. This is an identity of actual line-bundle classes, obtained from
effective normalized descent, rather than only an equality in a sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard

universe u

variable {k : Type u} [Field k]
  (A : Over (Spec (.of k))) [GrpObj A]
  {T : Over (Spec (.of k))}

def homogeneousEvaluationSection (a : T ⟶ A) : T ⟶ T ⊗ A := lift (𝟙 T) a

omit [GrpObj A] in
theorem homogeneousEvaluationSection_fst (a : T ⟶ A) :
    homogeneousEvaluationSection A a ≫ fst T A = 𝟙 T := lift_fst _ _

theorem homogeneousEvaluationSection_translation (a b : T ⟶ A) :
    homogeneousEvaluationSection A b ≫ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a = homogeneousEvaluationSection A (a * b) := by
  apply hom_ext <;> simp [homogeneousEvaluationSection, Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation, MonObj.comp_mul]

theorem homogeneousZero_translation (a : T ⟶ A) :
    lift (𝟙 T) (1 : T ⟶ A) ≫ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a = homogeneousEvaluationSection A a := by
  have h := homogeneousEvaluationSection_translation A a (1 : T ⟶ A)
  change homogeneousEvaluationSection A (1 : T ⟶ A) ≫ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a = homogeneousEvaluationSection A a
  simpa only [mul_one] using h

variable [IsAlgClosed k] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom]
  [GeometricallyIntegral A.hom] [IsLocallyNoetherian T.left]
  (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left)
  (hq : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A T q)
  (hzero : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift (𝟙 T) (1 : T ⟶ A)).left q = 1)

include hq hzero in
set_option backward.isDefEq.respectTransparency false in
theorem nativeHomogeneous_translation_class (a : T ⟶ A) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left q =
      q * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (homogeneousEvaluationSection A a).left q) := by
  have hrel : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T)
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) q := by
    have h := hq T (𝟙 T) a
    have hi : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map (𝟙 T).op q = q :=
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map_id_apply (op T) q
    rw [hi] at h
    exact h
  have hn := NormalizedRelativePicardInjection.Construction.normalizedProductClass_eq_of_relative_eq A _ q hrel
  rw [FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_of_axis A T q hzero] at hn
  have hs : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift (𝟙 T) (1 : T ⟶ A)).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left q) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (homogeneousEvaluationSection A a).left q := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
      (congrArg Over.Hom.left (homogeneousZero_translation A a))
  have hd : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left q =
      FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A T (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left q) *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A).left
          (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift (𝟙 T) (1 : T ⟶ A)).left
            (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left q)) := by
    exact (Quotients.FiniteDescent.PicardNormalizationEq.Construction.PicardNormalization.decompose (fst T A).left
      (lift (𝟙 T) (1 : T ⟶ A)).left (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left q)).symm
  rw [hn, hs] at hd
  exact hd

def nativeHomogeneous_evaluateClass (a : T ⟶ A) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (homogeneousEvaluationSection A a).left q

include hq hzero in
set_option backward.isDefEq.respectTransparency false in
theorem nativeHomogeneous_evaluateClass_mul (a b : T ⟶ A) :
    nativeHomogeneous_evaluateClass A q (a * b) = nativeHomogeneous_evaluateClass A q a * nativeHomogeneous_evaluateClass A q b := by
  have h := congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (homogeneousEvaluationSection A b).left)
    (nativeHomogeneous_translation_class A q hq hzero a)
  rw [map_mul] at h
  have ht : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (homogeneousEvaluationSection A b).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left q) = nativeHomogeneous_evaluateClass A q (a * b) := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
      (congrArg Over.Hom.left (homogeneousEvaluationSection_translation A a b))
  have hb (r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (homogeneousEvaluationSection A b).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A).left r) = r := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ r) = r
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    have hf : (homogeneousEvaluationSection A b).left ≫ (fst T A).left = 𝟙 T.left :=
      congrArg Over.Hom.left (homogeneousEvaluationSection_fst A b)
    rw [hf]
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id r
  rw [ht, hb] at h
  exact h.trans (mul_comm _ _)

include hzero in
omit [IsAlgClosed k] [IsProper A.hom] [Smooth A.hom]
  [GeometricallyIntegral A.hom] [IsLocallyNoetherian T.left] in
theorem nativeHomogeneous_evaluateClass_one : nativeHomogeneous_evaluateClass A q (1 : T ⟶ A) = 1 := hzero

def nativeHomogeneous_evaluationHom : (T ⟶ A) →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left where
  toFun := nativeHomogeneous_evaluateClass A q
  map_one' := nativeHomogeneous_evaluateClass_one A q hzero
  map_mul' := nativeHomogeneous_evaluateClass_mul A q hq hzero

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardEvaluation.Construction
