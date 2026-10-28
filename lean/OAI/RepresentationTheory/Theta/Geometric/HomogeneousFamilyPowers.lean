import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation

/-! # Homogeneous Family Powers -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomogeneousFamilyPowers

noncomputable section

/-! A normalized homogeneous line bundle pulls back under actual
integer multiplication as its tensor power. This supplies the
cohomological restriction needed for Picard surjectivity. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

theorem evaluateClass_baseChange {T U : Over (Spec (.of k))}
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) (f : U ⟶ T) (a : U ⟶ A.scheme) :
    AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q) a =
      AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift f a).left q := by
  have H : AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluationSection A a ≫ (f ▷ A.scheme) = lift f a := by
    apply hom_ext <;> simp [AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluationSection]
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluationSection A a).left
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ▷ A.scheme).left q) = _
  rw [← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun t => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t q) (congrArg Over.Hom.left H)

theorem homogeneous_family_zpow_class [IsAlgClosed k] {T : Over (Spec (.of k))}
    [CompactSpace T.left] [QuasiSeparatedSpace T.left]
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hq : A.IsHomogeneousPicardClass T q)
    (hzero : AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1) (n : ℤ) :
    AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (T ◁ ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n)).left q = q ^ n := by
  let U := T ⊗ A.scheme
  let f := fst T A.scheme
  let r := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q
  have : CompactSpace U.left := by
    change CompactSpace (CategoryTheory.Limits.pullback T.hom A.scheme.hom : Scheme)
    infer_instance
  have : QuasiSeparatedSpace U.left := by
    change QuasiSeparatedSpace (CategoryTheory.Limits.pullback T.hom A.scheme.hom : Scheme)
    exact quasiSeparatedSpace_of_quasiSeparated (CategoryTheory.Limits.pullback.fst T.hom A.scheme.hom)
  have hr : A.IsHomogeneousPicardClass U r := hq.pullback A f
  have hz : AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left r = 1 := by
    change AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left (AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (f ▷ A.scheme).left q) = 1
    rw [AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.zero_class_naturality, hzero, map_one]
  have H := (AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluationHom A r hr hz).map_zpow (snd T A.scheme) n
  change AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A r ((snd T A.scheme) ^ n) = (AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A r (snd T A.scheme)) ^ n at H
  have h₀ : lift f (snd T A.scheme) = 𝟙 U := by
    apply hom_ext <;> simp [f, U]
  have hₙ : lift f ((snd T A.scheme) ^ n) = T ◁ ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n) := by
    apply hom_ext <;> simp [f, GrpObj.comp_zpow]
  change AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q) _ =
    (AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q) _) ^ n at H
  rw [evaluateClass_baseChange, evaluateClass_baseChange, h₀, hₙ] at H
  have hid : AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (𝟙 U.left) q = q := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q
  exact H.trans (congrArg (fun z : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass U.left => z ^ n) hid)

theorem homogeneous_family_power_class [IsAlgClosed k] {T : Over (Spec (.of k))}
    [CompactSpace T.left] [QuasiSeparatedSpace T.left]
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hq : A.IsHomogeneousPicardClass T q)
    (hzero : AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1) (n : ℕ) :
    AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (T ◁ ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n)).left q = q ^ n := by
  simpa only [zpow_natCast] using homogeneous_family_zpow_class A q hq hzero (n : ℤ)

theorem homogeneous_family_inverse_class [IsAlgClosed k] {T : Over (Spec (.of k))}
    [CompactSpace T.left] [QuasiSeparatedSpace T.left]
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hq : A.IsHomogeneousPicardClass T q)
    (hzero : AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1) :
    AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (T ◁ ((𝟙 A.scheme : A.scheme ⟶ A.scheme)⁻¹)).left q = q⁻¹ := by
  simpa only [zpow_neg_one] using homogeneous_family_zpow_class A q hq hzero (-1 : ℤ)

end

end OAI.RepresentationTheory.Theta.Geometric.HomogeneousFamilyPowers
