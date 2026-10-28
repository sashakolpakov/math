import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberSpectrum
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Varying Dual Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction

noncomputable section

/-! Reduction of a varying family over dual numbers is a surjective
closed immersion. Its actual special fiber has the same underlying opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (k : Type) [Field k]

instance dualBaseReduction_closed : IsClosedImmersion (Smooth.AffineDualProduct.dualBaseReduction k) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) (fun a => ⟨(a, 0), rfl⟩)

instance dualBaseReduction_surjective : Surjective (Smooth.AffineDualProduct.dualBaseReduction k) :=
  Dual.NumberSpectrum.dualNumberOrigin_surjective

def dualFamilyReduction (X : Over (Spec (.of (DualNumber k)))) :
    ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X).left ⟶ X.left :=
  pullback.fst X.hom (Smooth.AffineDualProduct.dualBaseReduction k)

attribute [local implicit_reducible] dualFamilyReduction

instance dualFamilyReduction_closed (X : Over (Spec (.of (DualNumber k)))) :
    IsClosedImmersion (dualFamilyReduction k X) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst X.hom (Smooth.AffineDualProduct.dualBaseReduction k)))

instance dualFamilyReduction_surjective (X : Over (Spec (.of (DualNumber k)))) :
    Surjective (dualFamilyReduction k X) :=
  inferInstanceAs (Surjective (pullback.fst X.hom (Smooth.AffineDualProduct.dualBaseReduction k)))

def dualFamilyReductionHomeomorph (X : Over (Spec (.of (DualNumber k)))) :
    ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X).left ≃ₜ X.left :=
  (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(dualFamilyReduction k X).isClosedEmbedding.isEmbedding,
      (dualFamilyReduction k X).surjective⟩).homeomorph

theorem dualFamilyReduction_opens_injective (X : Over (Spec (.of (DualNumber k)))) :
    Function.Injective (fun U : X.left.Opens => (dualFamilyReduction k X) ⁻¹ᵁ U) := by
  intro U V h
  ext x
  obtain ⟨y, rfl⟩ := (dualFamilyReduction k X).surjective x
  exact (SetLike.ext_iff.mp h) y

theorem dualFamilyReduction_affineOpen (X : Over (Spec (.of (DualNumber k))))
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen ((dualFamilyReduction k X) ⁻¹ᵁ U) :=
  hU.preimage (dualFamilyReduction k X)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction
