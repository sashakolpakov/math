import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv

/-! # Homogeneous Picard Evaluation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard

noncomputable section

/-! A normalized homogeneous line-bundle family evaluates multiplicatively
on points. This is an identity of actual line-bundle classes, obtained from
effective normalized descent, rather than only an equality in a sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {T : Over (Spec (.of k))}

def evaluationSection (a : T ⟶ A.scheme) : T ⟶ T ⊗ A.scheme := lift (𝟙 T) a

theorem evaluationSection_fst (a : T ⟶ A.scheme) :
    evaluationSection A a ≫ fst T A.scheme = 𝟙 T := lift_fst _ _

theorem evaluationSection_translation (a b : T ⟶ A.scheme) :
    evaluationSection A b ≫ A.translation a = evaluationSection A (a * b) := by
  apply hom_ext <;> simp [evaluationSection, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation, MonObj.comp_mul]

theorem zero_translation (a : T ⟶ A.scheme) :
    Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ A.translation a = evaluationSection A a := by
  have h := evaluationSection_translation A a (1 : T ⟶ A.scheme)
  change evaluationSection A (1 : T ⟶ A.scheme) ≫ A.translation a = evaluationSection A a
  simpa only [mul_one] using h

variable [IsAlgClosed k] [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
  (hq : A.IsHomogeneousPicardClass T q)
  (hzero : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1)

include hq hzero in
theorem homogeneous_translation_class (a : T ⟶ A.scheme) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q =
      q * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A.scheme).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A a).left q) := by
  have hrel : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) q := by
    have h := hq T (𝟙 T) a
    have hi : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 T).op q = q :=
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_id_apply (op T) q
    rw [hi] at h
    exact h
  have hn := Picard.Inv.NormalizedPicard.normalizedClass_eq_of_picard_eq A _ q hrel
  rw [Picard.Inv.NormalizedPicard.normalizedClass_eq_self A T q hzero] at hn
  have hs : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A a).left q := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
      (congrArg Over.Hom.left (zero_translation A a))
  have hd := Picard.Inv.NormalizedPicard.normalizedClass_decompose A T (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q)
  rw [hn, hs] at hd
  exact hd.symm

def evaluateClass (a : T ⟶ A.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A a).left q

include hq hzero in
theorem evaluateClass_mul (a b : T ⟶ A.scheme) :
    evaluateClass A q (a * b) = evaluateClass A q a * evaluateClass A q b := by
  have h := congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A b).left)
    (homogeneous_translation_class A q hq hzero a)
  rw [map_mul] at h
  have ht : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A b).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.translation a).left q) = evaluateClass A q (a * b) := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ q
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
      (congrArg Over.Hom.left (evaluationSection_translation A a b))
  have hb (r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (evaluationSection A b).left
        (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst T A.scheme).left r) = r := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ r) = r
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    have hf : (evaluationSection A b).left ≫ (fst T A.scheme).left = 𝟙 T.left :=
      congrArg Over.Hom.left (evaluationSection_fst A b)
    rw [hf]
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id r
  rw [ht, hb] at h
  exact h.trans (mul_comm _ _)

include hzero in
omit [IsAlgClosed k] [CompactSpace T.left] [QuasiSeparatedSpace T.left] in
theorem evaluateClass_one : evaluateClass A q (1 : T ⟶ A.scheme) = 1 := hzero

def evaluationHom : (T ⟶ A.scheme) →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left where
  toFun := evaluateClass A q
  map_one' := evaluateClass_one A q hzero
  map_mul' := evaluateClass_mul A q hq hzero

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard
