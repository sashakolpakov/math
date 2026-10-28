import OAI.AlgebraicGeometry.Picard.Homomorphisms.Etale
import OAI.AlgebraicGeometry.Picard.Homomorphisms.MvPolynomial
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Affine -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) (hp : p.Prime)

theorem prime_eq_zero_spec (R : Type u) [CommRing R] (hR : (p : R) = 0) :
    (p : Γ(Spec (CommRingCat.of R), ⊤)) = 0 := by
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv hR
  simpa only [map_natCast, map_zero] using h

/-- The sheafwise construction agrees with the usual affine Frobenius. -/
theorem absoluteFrobenius_spec (R : Type u) [CommRing R] (hR : (p : R) = 0) :
    Frobenius.Construction.absoluteFrobenius p hp (Spec (CommRingCat.of R)) (prime_eq_zero_spec p R hR) =
      Spec.map (CommRingCat.ofHom (Frobenius.Construction.powerRingHom p hp R hR)) := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Frobenius.Construction.absoluteFrobenius p hp (Spec (CommRingCat.of R)) (prime_eq_zero_spec p R hR)).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom (Frobenius.Construction.powerRingHom p hp R hR))).appTop
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext r
  exact (map_pow (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r p).symm

theorem mvPolynomial_coefficient_pushout (R S : Type u) [CommRing R] [CommRing S]
    (σ : Type) (f : R →+* S) :
    IsPushout (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))
      (CommRingCat.ofHom f)
      (CommRingCat.ofHom (MvPolynomial.map f : MvPolynomial σ R →+* MvPolynomial σ S))
      (CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial σ S)) := by
  algebraize [f]
  let : Algebra (MvPolynomial σ R) (MvPolynomial σ S) :=
    MvPolynomial.algebraMvPolynomial
  exact CommRingCat.isPushout_of_isPushout R (MvPolynomial σ R) S (MvPolynomial σ S)

theorem prime_eq_zero_mvPolynomial (R : Type u) [CommRing R]
    (hR : (p : R) = 0) (σ : Type) : (p : MvPolynomial σ R) = 0 := by
  have h := congrArg (MvPolynomial.C : R →+* MvPolynomial σ R) hR
  simpa only [map_natCast, map_zero] using h

theorem mvPolynomial_expand_comp_map_power (R : Type u) [CommRing R]
    (hR : (p : R) = 0) (σ : Type) :
    (MvPolynomial.expand p).toRingHom.comp (MvPolynomial.map (Frobenius.Construction.powerRingHom p hp R hR)) =
      Frobenius.Construction.powerRingHom p hp (MvPolynomial σ R) (prime_eq_zero_mvPolynomial p R hR σ) := by
  ext r <;> simp [Frobenius.Construction.powerRingHom, map_pow]

set_option backward.isDefEq.respectTransparency.types false in
/-- The coefficient Frobenius square for polynomial algebras is a pullback. -/
theorem polynomial_frobenius_baseChange (R : Type u) [CommRing R]
    (hR : (p : R) = 0) (σ : Type) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (Frobenius.Construction.powerRingHom p hp R hR)
        : MvPolynomial σ R →+* MvPolynomial σ R)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R)))
      (Frobenius.Construction.absoluteFrobenius p hp (Spec (CommRingCat.of R)) (prime_eq_zero_spec p R hR)) := by
  rw [absoluteFrobenius_spec p hp R hR]
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (mvPolynomial_coefficient_pushout R R σ (Frobenius.Construction.powerRingHom p hp R hR))

set_option backward.isDefEq.respectTransparency.types false in
/-- Polynomial relative Frobenius is the coordinate power map, followed
by the canonical isomorphism with the scheme-theoretic base change. -/
theorem relativeFrobenius_polynomial_factorization (R : Type u) [CommRing R]
    (hR : (p : R) = 0) (σ : Type) :
    (Frobenius.Construction.relativeFrobenius p hp (prime_eq_zero_spec p R hR)
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial σ R))))).left =
      Spec.map (CommRingCat.ofHom (MvPolynomial.expand p (R := R) (σ := σ)).toRingHom) ≫
        (polynomial_frobenius_baseChange p hp R hR σ).isoPullback.hom := by
  apply pullback.hom_ext
  · erw [Frobenius.Construction.relativeFrobenius_comp_fst, Category.assoc, IsPullback.isoPullback_hom_fst,
      absoluteFrobenius_spec p hp (MvPolynomial σ R) (prime_eq_zero_mvPolynomial p R hR σ),
      ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (mvPolynomial_expand_comp_map_power p hp R hR σ).symm
  · change (Frobenius.Construction.relativeFrobenius p hp (prime_eq_zero_spec p R hR)
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial σ R))))).left ≫
      (Frobenius.Construction.frobeniusTwist p hp (prime_eq_zero_spec p R hR)
        (Over.mk (Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : R →+* MvPolynomial σ R))))).hom = _
    erw [Over.w, Category.assoc, IsPullback.isoPullback_hom_snd, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R)) = _
    congr 1
    ext r
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Relative Frobenius of affine space is flat. -/
theorem relativeFrobenius_polynomial_flat (R : Type u) [CommRing R]
    (hR : (p : R) = 0) (σ : Type) [Finite σ] :
    Flat (Frobenius.Construction.relativeFrobenius p hp (prime_eq_zero_spec p R hR)
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial σ R))))).left := by
  rw [relativeFrobenius_polynomial_factorization p hp R hR σ]
  have hflat : Flat (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand p (R := R) (σ := σ)).toRingHom)) :=
    Flat.SpecMap_iff.mpr (Homomorphisms.MvPolynomial.Construction.mvPolynomial_expand_flat R p hp.ne_zero σ)
  exact MorphismProperty.comp_mem @Flat _ _ hflat inferInstance

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine.Construction
