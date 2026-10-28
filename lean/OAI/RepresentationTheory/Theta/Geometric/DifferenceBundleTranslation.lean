import OAI.RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

/-! # Difference Bundle Translation -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferenceBundleTranslation

noncomputable section

/-! Translation invariance of the actual algebraic difference bundle,
deduced from invariance of its original line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem algebraicDifferenceBundle_preserved {X Z : Scheme.{u}}
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (p₁ p₂ m : Z ⟶ X) (t : X ⟶ X) (a : Z ⟶ Z)
    (hL : Nonempty ((L.pullback t).sheaf ≅ L.sheaf))
    (h₁ : a ≫ p₁ = p₁ ≫ t) (h₂ : a ≫ p₂ = p₂) (hm : a ≫ m = m ≫ t) :
    Nonempty (((AlgebraicDifferenceBundle.algebraicDifferenceBundle L p₁ p₂ m).pullback a).sheaf ≅
      (AlgebraicDifferenceBundle.algebraicDifferenceBundle L p₁ p₂ m).sheaf) := by
  have ht : Picard.PicardPullback.picardPullback t (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    Quotient.sound hL
  have h := Picard.PicardPullback.algebraicDifferenceBundle_pullback_class L p₁ p₂ m a
  rw [h₁, h₂, hm, ← Picard.PicardPullback.picardPullback_comp, ← Picard.PicardPullback.picardPullback_comp, ht] at h
  exact Quotient.exact h

def groupTranslation {S : Scheme.{u}} (A : Over S) [GrpObj A]
    (p : Over.mk (𝟙 S) ⟶ A) : A ⟶ A :=
  (𝟙 A) * (Over.mkIdTerminal.from A ≫ p)

theorem groupTranslation_comp {S : Scheme.{u}} {A T : Over S} [GrpObj A]
    (p : Over.mk (𝟙 S) ⟶ A) (f : T ⟶ A) :
    f ≫ groupTranslation A p = f * (Over.mkIdTerminal.from T ≫ p) := by
  rw [groupTranslation, MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  exact Over.mkIdTerminal.hom_ext _ _

theorem groupTranslation_one {S : Scheme.{u}} (A : Over S) [GrpObj A] :
    groupTranslation A 1 = 𝟙 A := by
  rw [groupTranslation, MonObj.comp_one, mul_one]

theorem groupTranslation_mul {S : Scheme.{u}} (A : Over S) [GrpObj A]
    (p q : Over.mk (𝟙 S) ⟶ A) :
    groupTranslation A p ≫ groupTranslation A q = groupTranslation A (p * q) := by
  rw [groupTranslation_comp, groupTranslation, groupTranslation, MonObj.comp_mul, mul_assoc]

theorem firstTranslation_comp {S : Scheme.{u}} (A : Over S) [GrpObj A]
    (p q : Over.mk (𝟙 S) ⟶ A) :
    (groupTranslation A p ⊗ₘ 𝟙 A) ≫ (groupTranslation A q ⊗ₘ 𝟙 A) =
      groupTranslation A (p * q) ⊗ₘ 𝟙 A := by
  rw [tensorHom_comp_tensorHom, groupTranslation_mul, Category.id_comp]

theorem firstTranslation_mul {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (p : Over.mk (𝟙 S) ⟶ A) :
    (groupTranslation A p ⊗ₘ 𝟙 A) ≫ μ[A] = μ[A] ≫ groupTranslation A p := by
  have hmul : μ[A] = fst A A * snd A A := by
    change μ[A] = lift (fst A A) (snd A A) ≫ μ[A]
    simp
  rw [hmul, MonObj.comp_mul]
  rw [tensorHom_fst, tensorHom_snd, Category.comp_id, groupTranslation_comp,
    groupTranslation_comp]
  ac_rfl

theorem firstTranslation_zeroSlice {S : Scheme.{u}} (A : Over S) [GrpObj A]
    (p : Over.mk (𝟙 S) ⟶ A) :
    lift (𝟙 A) (1 : A ⟶ A) ≫ (groupTranslation A p ⊗ₘ 𝟙 A) =
      groupTranslation A p ≫ lift (𝟙 A) (1 : A ⟶ A) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem abelianDifferenceBundle_firstTranslation {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (p : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.scheme)
    (hL : Nonempty ((L.pullback (groupTranslation A.scheme p).left).sheaf ≅ L.sheaf)) :
    Nonempty (((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
        (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf) := by
  apply algebraicDifferenceBundle_preserved L _ _ _ (groupTranslation A.scheme p).left _ hL
  · exact congrArg Over.Hom.left (tensorHom_fst (groupTranslation A.scheme p) (𝟙 A.scheme))
  · exact congrArg Over.Hom.left
      ((tensorHom_snd (groupTranslation A.scheme p) (𝟙 A.scheme)).trans (Category.comp_id _))
  · exact congrArg Over.Hom.left (firstTranslation_mul A.scheme p)

end

end OAI.RepresentationTheory.Theta.Geometric.DifferenceBundleTranslation
