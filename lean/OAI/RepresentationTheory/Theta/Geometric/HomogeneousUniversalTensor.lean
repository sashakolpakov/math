import OAI.RepresentationTheory.Theta.Geometric.MultiplicativeFamilyCriterion
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousFamilyPowers

/-! # Homogeneous Universal Tensor -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomogeneousUniversalTensor

noncomputable section

/-! A normalized homogeneous family satisfies one actual tensor identity
over the universal pair, with no finite-type assumption on its parameter. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))

theorem multiplicative_family_of_homogeneous {T : Over (Spec (.of K))}
    [CompactSpace T.left] [QuasiSeparatedSpace T.left]
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hq : A.IsHomogeneousPicardClass T q)
    (hz : Picard.PicardPullback.picardPullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left q = 1) :
    MultiplicativeFamilyCriterion.IsMultiplicativeFamilyClass A T q := by
  let U := T ⊗ (A.scheme ⊗ A.scheme)
  let p := fst T (A.scheme ⊗ A.scheme)
  let x := snd T (A.scheme ⊗ A.scheme) ≫ fst A.scheme A.scheme
  let y := snd T (A.scheme ⊗ A.scheme) ≫ snd A.scheme A.scheme
  let r := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map p.op q
  have : IsProper (A.scheme ⊗ A.scheme).hom := by
    change IsProper (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom)
    infer_instance
  have : CompactSpace U.left := by
    change CompactSpace (pullback T.hom (A.scheme ⊗ A.scheme).hom : Scheme)
    infer_instance
  have : QuasiSeparatedSpace U.left := by
    change QuasiSeparatedSpace (pullback T.hom (A.scheme ⊗ A.scheme).hom : Scheme)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst T.hom (A.scheme ⊗ A.scheme).hom)
  have hr : A.IsHomogeneousPicardClass U r := hq.pullback A p
  have hz' : AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1 := hz
  have hrz : AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left r = 1 := by
    change AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left (AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (p ▷ A.scheme).left q) = 1
    rw [AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.zero_class_naturality, hz', map_one]
  have h := (AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluationHom A r hr hrz).map_mul x y
  change AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map p.op q) (x * y) =
    AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map p.op q) x *
      AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map p.op q) y at h
  rw [HomogeneousFamilyPowers.evaluateClass_baseChange, HomogeneousFamilyPowers.evaluateClass_baseChange, HomogeneousFamilyPowers.evaluateClass_baseChange] at h
  have hm : lift p (x * y) = T ◁ (fst A.scheme A.scheme * snd A.scheme A.scheme) := by
    apply hom_ext <;> simp [p, x, y, MonObj.comp_mul]
  have h₁ : lift p x = T ◁ fst A.scheme A.scheme := by
    apply hom_ext <;> simp [p, x]
  have h₂ : lift p y = T ◁ snd A.scheme A.scheme := by
    apply hom_ext <;> simp [p, y]
  rw [hm, h₁, h₂] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.HomogeneousUniversalTensor
