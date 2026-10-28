import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativePicard
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardNormalizationEq
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Line Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization

noncomputable section

/-! Normalize an actual product-family line along the identity section.
This commutes with parameter change and preserves its relative Picard class. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

def normalizedProductClass (T : Over S) (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left :=
  Quotients.FiniteDescent.PicardNormalizationEq.Construction.PicardNormalization.normalize (fst T A).left (lift (𝟙 T) (1 : T ⟶ A)).left c

theorem normalizedProductClass_axis (T : Over S) (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left (normalizedProductClass A T c) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass T.left :=
  Quotients.FiniteDescent.PicardNormalizationEq.Construction.PicardNormalization.restriction_normalize (fst T A).left
    (lift (𝟙 T) (1 : T ⟶ A)).left (congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A))) c

theorem normalizedProductClass_of_axis (T : Over S) (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left c = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass T.left) :
    normalizedProductClass A T c = c := by
  change c / Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left c) = c
  rw [h]
  change c / Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A).left 1 = c
  rw [map_one, div_one]

theorem normalizedProductClass_pullback {T U : Over S} (j : U ⟶ T)
    (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (normalizedProductClass A T c) =
      normalizedProductClass A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left c) := by
  change Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (j ⊗ₘ 𝟙 A).left
    (c / Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A).left
      (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (lift (𝟙 T) (1 : T ⟶ A)).left c)) = _
  rw [map_div]
  unfold normalizedProductClass Quotients.FiniteDescent.PicardNormalizationEq.Construction.PicardNormalization.normalize
  apply congrArg (fun z => Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (j ⊗ₘ 𝟙 A).left c / z)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst T A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left c)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst U A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 U) (1 : U ⟶ A)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left c))
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  apply congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f c)
  have he : ((j ⊗ₘ 𝟙 A) ≫ fst T A) ≫ lift (𝟙 T) (1 : T ⟶ A) =
      (fst U A ≫ lift (𝟙 U) (1 : U ⟶ A)) ≫ (j ⊗ₘ 𝟙 A) := by simp
  exact congrArg Over.Hom.left he

theorem normalizedProductClass_relative (T : Over S) (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (normalizedProductClass A T c) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) c := by
  have he : normalizedProductClass A T c = RelativePicard.Construction.RelativePicardBaseTwist.baseTwist A
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left c)⁻¹ c := by
    change c / Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A).left _ = Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (fst T A).left _ * c
    rw [map_inv, div_eq_mul_inv, mul_comm]
    rfl
  rw [he]
  exact RelativePicard.Construction.RelativePicardBaseTwist.toRelativePicard_baseTwist_class A _ c

def normalizedProductBundle (T : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left :=
  (normalizedProductClass A T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).out

theorem normalizedProductBundle_class (T : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedProductBundle A T L) = normalizedProductClass A T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
  Quotient.out_eq _

def normalizedProductBundle_axis (T : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left) :
    (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj
        (normalizedProductBundle A T L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left := by
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedProductBundle A T L)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass T.left := by
    rw [normalizedProductBundle_class, normalizedProductClass_axis]
  exact Classical.choice (Quotient.exact hc)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization
