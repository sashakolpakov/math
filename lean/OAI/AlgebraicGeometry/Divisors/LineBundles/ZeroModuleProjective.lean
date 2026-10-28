import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.RankOneProjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base

/-! # Zero Module Projective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ZeroModuleProjective.BundleCycles

noncomputable section

/-! The augmented projective spectrum of a module with an empty
basis is the coefficient scheme through the actual projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M)

include b in
theorem symmetricAugmentedProjective_isIso_of_basis_card_zero (h : Nat.card ι = 0) :
    IsIso (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) := by
  let : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.card_eq_fintype_card.symm.trans h)
  let : Subsingleton M := b.repr.subsingleton
  let : Unique M := ⟨⟨0⟩, fun x => Subsingleton.elim x 0⟩
  let e : (R × M) ≃ₗ[R] R := LinearEquiv.prodUnique
  have he : (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).hom ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R R =
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) := SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over e.symm.toLinearMap e.symm.surjective
  rw [← he]
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ZeroModuleProjective.BundleCycles
