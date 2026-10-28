import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceBundle
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeTranslationClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup

/-! # Relative Difference Eq -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceEq.Geometric

noncomputable section

section

/-! The actual normalized difference line vanishes in the original
relative Picard sheaf exactly when translation preserves the normalized
original line's class. No cube identity or dual is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    {T : Over S} (a : T ⟶ A.scheme)

theorem relativeRigidifiedDifference_value :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      (Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T)
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left
          (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd T A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)))) *
      ((Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T)
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd T A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))))⁻¹ := by
  let M := RelativeDifferenceBundle.Geometric.identityNormalizedLine A L
  have hm : (a ⊗ₘ 𝟙 A.scheme) ≫ μ[A.scheme] = A.translation a ≫ snd T A.scheme := by
    rw [A.translation_snd, Hom.mul_def]
    have h := lift_fst_comp_snd_comp a (𝟙 A.scheme)
    simp only [Category.comp_id] at h
    exact congrArg (fun v => v ≫ μ[A.scheme]) h.symm
  have h₁ : (a ⊗ₘ 𝟙 A.scheme).left ≫ (fst A.scheme A.scheme).left =
      (fst T A.scheme).left ≫ a.left := congrArg Over.Hom.left (tensorHom_fst a (𝟙 A.scheme))
  have h₂ : (a ⊗ₘ 𝟙 A.scheme).left ≫ (snd A.scheme A.scheme).left =
      (snd T A.scheme).left := by
    have h := congrArg Over.Hom.left (tensorHom_snd a (𝟙 A.scheme))
    exact h.trans (Category.comp_id _)
  have hmul : (a ⊗ₘ 𝟙 A.scheme).left ≫ μ[A.scheme].left =
      (A.translation a).left ≫ (snd T A.scheme).left := congrArg Over.Hom.left hm
  have he := RepresentationTheory.Theta.Geometric.Picard.PicardPullback.algebraicDifferenceBundle_pullback_class M
    (fst A.scheme A.scheme).left (snd A.scheme A.scheme).left μ[A.scheme].left
    (a ⊗ₘ 𝟙 A.scheme).left
  rw [h₁, h₂, hmul, ← RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, ← RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp] at he
  have hb : (Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst T A.scheme).left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))) = 1 :=
    (AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality.baseBundle_relativePicardClass_trivial A.scheme T (M.pullback a.left)).trans
      (Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one A.scheme T)
  change (Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RepresentationTheory.Theta.Geometric.AlgebraicDifferenceBundle.algebraicDifferenceBundle M (fst A.scheme A.scheme).left
      (snd A.scheme A.scheme).left μ[A.scheme].left).pullback (a ⊗ₘ 𝟙 A.scheme).left)) = _
  refine (congrArg (fun c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left =>
    (Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T) c) he).trans ?_
  let x : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T) :=
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd T A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
  let y : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T) :=
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst T A.scheme).left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
  let z : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T) :=
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd T A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)
  let φ := Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T
  have hy : φ y = 1 := hb
  change φ (x * y⁻¹ * z⁻¹) = φ x * (φ z)⁻¹
  rw [map_mul, map_mul, map_inv, map_inv, hy, inv_one, mul_one]

theorem relativeRigidifiedDifference_zero_iff_translation :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme T ↔
      A.TranslationInvariant a
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (snd T A.scheme).left)) := by
  rw [relativeRigidifiedDifference_value, Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one, mul_inv_eq_one]
  rfl

end

section

/-! Equality of actual difference-line values follows from the genuine
translation stabilizer. This provides descent on quotient fibers
without assuming a cube identity or a relative dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T : Over S}

theorem translation_relativeClass_comp (a b : T ⟶ A.scheme)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation b).left q) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (a * b)).left q := by
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q)
    (congrArg Over.Hom.left (A.translation_comp a b))

theorem translation_relativeClass_eq_of_div_invariant (a b : T ⟶ A.scheme)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (h : A.TranslationInvariant (a * b⁻¹) q) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left q) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation b).left q) := by
  have he := RelativeTranslationClasses.Geometric.translation_relativeClass_congr A b _ _ h
  have hcomp := congrArg (fun v : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) v)
    (translation_relativeClass_comp A b (a * b⁻¹) q)
  have hab : b * (a * b⁻¹) = a := by simp only [mul_left_comm b a, mul_inv_cancel, mul_one]
  have hmul := congrArg (fun z : T ⟶ A.scheme =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation z).left q)) hab
  exact hmul.symm.trans (hcomp.symm.trans he)

theorem relativeRigidifiedDifference_eq_of_div_zero (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (a b : T ⟶ A.scheme)
    (h : (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (a * b⁻¹) =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme T) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue b := by
  have ht := (relativeRigidifiedDifference_zero_iff_translation A L (a * b⁻¹)).mp h
  have he := translation_relativeClass_eq_of_div_invariant A a b
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (snd T A.scheme).left)) ht
  rw [relativeRigidifiedDifference_value, relativeRigidifiedDifference_value]
  exact congrArg (fun v => v *
    ((Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme T)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd T A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))))⁻¹) he

end

/-! Two original difference-line values coincide exactly when their
quotient point stabilizes the original line. Translation of equality
in the actual Picard sheaf proves both directions on every test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) {T : Over S}

theorem relativeRigidifiedDifference_div_zero_of_eq (a b : T ⟶ A.scheme)
    (h : (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue b) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (a * b⁻¹) =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme T := by
  let q := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (snd T A.scheme).left)
  have he : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation b).left q) := by
    rw [relativeRigidifiedDifference_value, relativeRigidifiedDifference_value] at h
    exact mul_right_cancel h
  have ht := RelativeTranslationClasses.Geometric.translation_relativeClass_congr A b⁻¹ _ _ he
  let pic := fun v : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) v
  have hcomp₁ := congrArg pic (translation_relativeClass_comp A b⁻¹ a q)
  have hcomp₂ := congrArg pic (translation_relativeClass_comp A b⁻¹ b q)
  have hmul := hcomp₁.symm.trans (ht.trans hcomp₂)
  have hright : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (b⁻¹ * b)).left q = q := by
    rw [inv_mul_cancel, A.translation_one]
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q
  have hleft := congrArg (fun z : T ⟶ A.scheme =>
    pic (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation z).left q)) (mul_comm b⁻¹ a)
  apply (relativeRigidifiedDifference_zero_iff_translation A L (a * b⁻¹)).mpr
  exact hleft.symm.trans (hmul.trans (congrArg pic hright))

theorem relativeRigidifiedDifference_eq_iff_div_zero (a b : T ⟶ A.scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
        (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue b ↔
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (a * b⁻¹) =
        AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme T :=
  ⟨relativeRigidifiedDifference_div_zero_of_eq A L a b,
    relativeRigidifiedDifference_eq_of_div_zero A L a b⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceEq.Geometric
