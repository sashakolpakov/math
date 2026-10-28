import OAI.AlgebraicGeometry.Picard.Homomorphisms.MvPolynomialRank
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Affine Frobenius Rank -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.AffineFrobeniusRank

noncomputable section

/-! The exact degree of relative Frobenius on affine space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem finrank_comp_targetIso {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IsFinite f] (e : Y ≅ Z) (z : Z) :
    (f ≫ e.hom).finrank z = f.finrank (e.inv z) := by
  have h : IsPullback (𝟙 X) f (f ≫ e.hom) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have he := Scheme.Hom.finrank_of_isPullback (𝟙 X) f (f ≫ e.hom) e.hom h (e.inv z)
  simpa [← Scheme.Hom.comp_apply] using he.symm

theorem relativeFrobenius_polynomial_finrank
    (p : ℕ) (hp : p.Prime) (R : Type u) [CommRing R]
    (hR : (p : R) = 0) (σ : Type) [Finite σ]
    (y : (Frobenius.Construction.frobeniusTwist p hp (Affine.Construction.prime_eq_zero_spec p R hR)
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial σ R))))).left) :
    (Frobenius.Construction.relativeFrobenius p hp (Affine.Construction.prime_eq_zero_spec p R hR)
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial σ R))))).left.finrank y = p ^ Nat.card σ := by
  let x : PrimeSpectrum (MvPolynomial σ R) :=
    (Affine.Construction.polynomial_frobenius_baseChange p hp R hR σ).isoPullback.inv y
  have : Nontrivial (MvPolynomial σ R) := x.nontrivial
  have : Nontrivial R := (MvPolynomial.C : R →+* MvPolynomial σ R).domain_nontrivial
  have hfree := MvPolynomialRank.Construction.mvPolynomial_expand_hasFiniteBasis R p hp.ne_zero σ
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand p (R := R) (σ := σ)).toRingHom)) := by
    rw [IsFinite.SpecMap_iff]
    exact hfree.finite
  have : Flat (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand p (R := R) (σ := σ)).toRingHom)) :=
    Flat.SpecMap_iff.mpr hfree.flat
  rw [Affine.Construction.relativeFrobenius_polynomial_factorization p hp R hR σ]
  erw [finrank_comp_targetIso,
    Scheme.Hom.finrank_SpecMap_eq_finrank hfree.finite hfree.flat]
  exact hfree.finrank _

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.AffineFrobeniusRank
