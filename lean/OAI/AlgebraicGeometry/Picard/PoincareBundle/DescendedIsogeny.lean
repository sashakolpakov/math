import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.DualPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescendedScalarComplement
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.Complement
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ComplementaryIsogeny
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveOverQuotient
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRankAnnihilation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupHomFlat

/-! # Descended Isogeny -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DescendedIsogeny

noncomputable section

/-!
# Isogeny geometry of the descended homomorphism

The complement of the original finite flat map is constructed using the
finite-flat degree's annihilation of its full subgroup-scheme kernel.
Positive scalar geometry on the actual dual then proves surjectivity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {k : Type u} [Field k] {A B Q : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj Q]
  [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
  (DB : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
  (f : A ⟶ B) [IsMonHom f] [Surjective f.left]
  (m : B ⟶ DB.abelian) [IsMonHom m] (g : DB.abelian ⟶ Q) [IsMonHom g]
  (φ : A ⟶ Q) [IsMonHom φ] [IsFinite φ.left] [Flat φ.left] [Surjective φ.left]
  (h : f ≫ m ≫ g = φ) (v : Q ⟶ DB.abelian) (n : ℕ) (hn : 0 < n)
  (hv : g ≫ v = (𝟙 DB.abelian) ^ n)

include h hn hv

/-- The descended group homomorphism is finite, flat and surjective as an actual scheme morphism. -/
theorem finite_flat_surjective : IsFinite m.left ∧ Flat m.left ∧ Surjective m.left := by
  have hfin : IsFinite (f ≫ m ≫ g).left := by rw [h]; infer_instance
  have hmfin : IsFinite m.left := Finite.DualPullback.finite_of_finite_pullback f m g
  have : EffectiveEpi φ := EffectiveOverQuotient.affine_effective φ
  have : EffectiveEpi (φ ⊗ₘ φ) := EffectiveOverQuotient.tensor_effective φ
  let s : Spec (.of k) := IsLocalRing.closedPoint k
  let d := φ.left.finrank (η[Q].left s)
  have hd : 0 < d := (φ.left.one_le_finrank_iff_surjective.mpr inferInstance) (η[Q].left s)
  have hk : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1 :=
    fun T x hx => AbelianScheme.CartierDuality.IntrinsicRankAnnihilation.Construction.NormCharacters.kernel_killed_by_degree k φ s T x hx
  let t := ComplementaryIsogeny.complement φ d hk
  have : IsMonHom t := ComplementaryIsogeny.complement_isMonHom φ d hk
  have ht : t ≫ φ = (𝟙 Q) ^ d := ComplementaryIsogeny.right_complement φ d hk
  have : IsFinite ((𝟙 DB.abelian) ^ n).left := AbelianScheme.CartierDuality.RelativeTorsion.Construction.RelativeAbelian.finite_positive_dual_power B DB n hn
  have : EffectiveEpi ((𝟙 DB.abelian) ^ n) := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.Multiplication.effectiveEpi_power_of_isFinite DB.abelian n
  have hr : DescendedScalarComplement.complement f g t ≫ m = (𝟙 DB.abelian) ^ d :=
    DescendedScalarComplement.right_complement f m g φ t h d ht v n hv
  have : IsFinite ((𝟙 DB.abelian) ^ d).left := AbelianScheme.CartierDuality.RelativeTorsion.Construction.RelativeAbelian.finite_positive_dual_power B DB d hd
  have : Surjective ((𝟙 DB.abelian) ^ d).left := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.Multiplication.surjective_power_of_isFinite DB.abelian d
  have hmsurj : Surjective m.left := Scalar.Complement.surjective_of_scalar_complement
    m (DescendedScalarComplement.complement f g t) d hr
  exact ⟨hmfin, AbelianScheme.IsogenyQuotient.Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat m, hmsurj⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DescendedIsogeny
