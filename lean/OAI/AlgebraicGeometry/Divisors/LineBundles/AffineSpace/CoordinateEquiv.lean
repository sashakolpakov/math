import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.IrreducibleDef

/-! # Coordinate Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles

noncomputable section

/-! # LineBundleCycles: empty, reindexed, and successor relative affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {ι κ : Type} (X : Scheme.{0})

def affineSpaceReindexEquiv (e : ι ≃ κ) : AffineSpace ι X ≅ AffineSpace κ X where
  hom := AffineSpace.reindex e.symm X
  inv := AffineSpace.reindex e X
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp

theorem affineSpaceReindexEquiv_over (e : ι ≃ κ) :
    (affineSpaceReindexEquiv X e).hom ≫ (AffineSpace κ X ↘ X) = (AffineSpace ι X ↘ X) :=
  AffineSpace.reindex_over _ _

def affineSpaceEmptyEquiv (ι : Type) [IsEmpty ι] : AffineSpace ι X ≅ X where
  hom := AffineSpace ι X ↘ X
  inv := AffineSpace.homOfVector (𝟙 X) (fun i : ι => isEmptyElim i)
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp
    · exact isEmptyElim
  inv_hom_id := AffineSpace.homOfVector_over _ _

irreducible_def affineSpaceSuccEquiv (n : ℕ) :
    AffineSpace (Fin (n + 1)) X ≅ AffineSpace PUnit (AffineSpace (Fin n) X) :=
  affineSpaceReindexEquiv X
    (((finSuccEquiv n).trans (Equiv.optionEquivSumPUnit (Fin n))).trans (Equiv.sumComm _ _)) ≪≫
      Sum.BundleCycles.affineSpaceSumEquiv PUnit (Fin n) X

theorem affineSpaceSuccEquiv_over (n : ℕ) :
    (affineSpaceSuccEquiv X n).hom ≫
      ((AffineSpace PUnit (AffineSpace (Fin n) X) ↘ AffineSpace (Fin n) X) ≫
        (AffineSpace (Fin n) X ↘ X)) = (AffineSpace (Fin (n + 1)) X ↘ X) := by
  rw [affineSpaceSuccEquiv_def]
  change (_ ≫ (Sum.BundleCycles.affineSpaceSumEquiv PUnit (Fin n) X).hom) ≫ _ = _
  rw [Category.assoc, Sum.BundleCycles.affineSpaceSumEquiv_over, affineSpaceReindexEquiv_over]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles
