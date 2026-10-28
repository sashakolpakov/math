import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation
import OAI.RepresentationTheory.Theta.Geometric.ConstantPicardPullback

/-! # Homogeneous Line Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousLinePowers

noncomputable section

/-! Homogeneity of an actual line class over a field forces its pullback
along every power map to be the corresponding tensor power. The identity
is proved in the native Picard group by normalized effective descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] {g : ℕ}
  (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

def constantLineFamily (T : Over (Spec (.of k))) (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) :
    HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left :=
  HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T A.scheme).left q

theorem constantLineFamily_baseChange {T U : Over (Spec (.of k))}
    (f : U ⟶ T) (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) :
    (HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op (constantLineFamily A T q) =
      constantLineFamily A U q := by
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ 𝟙 A.scheme).left
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T A.scheme).left q) = _
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun h => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass h q)
    (congrArg Over.Hom.left (by simp :
      (f ⊗ₘ 𝟙 A.scheme) ≫ snd T A.scheme = snd U A.scheme))

def IsHomogeneousLineClass (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) : Prop :=
  A.IsHomogeneousPicardClass (Over.mk (𝟙 (Spec (.of k))))
    (constantLineFamily A (Over.mk (𝟙 (Spec (.of k)))) q)

theorem IsHomogeneousLineClass.family {q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left}
    (hq : IsHomogeneousLineClass A q) (T : Over (Spec (.of k))) :
    A.IsHomogeneousPicardClass T (constantLineFamily A T q) := by
  let f : T ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk T.hom (by simp)
  have h := hq.pullback A f
  rw [constantLineFamily_baseChange] at h
  exact h

theorem constantLineFamily_normalized (T : Over (Spec (.of k)))
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (constantLineFamily A T q) = 1 := by
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T A.scheme).left q) = 1
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have he : (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left ≫ (snd T A.scheme).left =
      T.hom ≫ (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme).left := by
    have h : Isogenies.NeighborCounting.PoincareNormalization.familyZero A T ≫ snd T A.scheme = (1 : T ⟶ A.scheme) := by
      simp [Isogenies.NeighborCounting.PoincareNormalization.familyZero]
    exact (congrArg Over.Hom.left h).trans (by rfl)
  rw [he]
  exact RepresentationTheory.Theta.Geometric.ConstantPicardPullback.picardPullback_constant k T.hom _ q

theorem evaluate_constantLineFamily {T : Over (Spec (.of k))}
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) (a : T ⟶ A.scheme) :
    PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A (constantLineFamily A T q) a = HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a.left q := by
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluationSection A a).left
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T A.scheme).left q) = _
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun h => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass h q)
    (congrArg Over.Hom.left (lift_snd (𝟙 T) a))

variable [IsAlgClosed k]

theorem homogeneousLineClass_pullback_pow
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) (hq : IsHomogeneousLineClass A q)
    {T : Over (Spec (.of k))} [CompactSpace T.left] [QuasiSeparatedSpace T.left]
    (a : T ⟶ A.scheme) (n : ℕ) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ^ n).left q = (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a.left q) ^ n := by
  have h := map_pow (PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluationHom A (constantLineFamily A T q)
    (hq.family A T) (constantLineFamily_normalized A T q)) a n
  change PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A (constantLineFamily A T q) (a ^ n) =
    PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A (constantLineFamily A T q) a ^ n at h
  simpa only [evaluate_constantLineFamily] using h

theorem homogeneousLineClass_power
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) (hq : IsHomogeneousLineClass A q)
    [CompactSpace A.scheme.left] [QuasiSeparatedSpace A.scheme.left] (n : ℕ) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 A.scheme) ^ n).left q = q ^ n := by
  simpa only [Over.id_left, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] using
    homogeneousLineClass_pullback_pow A q hq (𝟙 A.scheme) n

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousLinePowers
