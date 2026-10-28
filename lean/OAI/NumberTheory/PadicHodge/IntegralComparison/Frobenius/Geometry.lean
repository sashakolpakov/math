import Mathlib

/-! # Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

noncomputable section

/-!
# IntegralComparison: Frobenius on the geometric fiber

Arithmetic Frobenius is the q-power automorphism of the algebraic closure
of a finite field. Its inverse is geometric Frobenius. Both fix the base
field, and hence induce actual scheme automorphisms of every geometric
fiber. Cohomological pullback is kept separate from these scheme maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable (p a : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [Fintype k] [CharP k p]

/-- Arithmetic q-Frobenius on the algebraic closure, fixing the finite base field. -/
def arithmeticFrobenius (hcard : Fintype.card k = p ^ a) :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k where
  toRingEquiv := iterateFrobeniusEquiv (AlgebraicClosure k) p a
  commutes' x := by
    change (algebraMap k (AlgebraicClosure k) x) ^ (p ^ a) = _
    rw [← map_pow, ← hcard, FiniteField.pow_card]

@[simp]
lemma arithmeticFrobenius_apply (hcard : Fintype.card k = p ^ a)
    (x : AlgebraicClosure k) : arithmeticFrobenius p a k hcard x = x ^ (p ^ a) := rfl

/-- Geometric Frobenius, as a field automorphism. -/
def geometricFrobenius (hcard : Fintype.card k = p ^ a) :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k :=
  (arithmeticFrobenius p a k hcard).symm

lemma geometricFrobenius_pow (hcard : Fintype.card k = p ^ a)
    (x : AlgebraicClosure k) :
    geometricFrobenius p a k hcard x ^ (p ^ a) = x :=
  (arithmeticFrobenius p a k hcard).apply_symm_apply x

section BaseChange

variable {k}
variable {L : Type u} [Field L] [Algebra k L]
omit [Fintype k]

/-- The geometric fiber over a specified extension field. -/
abbrev geometricFiber {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))

/-- The scheme automorphism corresponding contravariantly to a field automorphism. -/
def scalarSchemeIso (σ : L ≃ₐ[k] L) :
    Spec (CommRingCat.of L) ≅ Spec (CommRingCat.of L) :=
  Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op

lemma scalarSchemeIso_over (σ : L ≃ₐ[k] L) :
    (scalarSchemeIso σ).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- Field automorphisms act on the scheme-theoretic geometric fiber. -/
def geometricFiberIso {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : L ≃ₐ[k] L) : geometricFiber (L := L) f ≅ geometricFiber (L := L) f where
  hom := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (scalarSchemeIso σ).hom) (by
      rw [Category.assoc, scalarSchemeIso_over]
      exact pullback.condition)
  inv := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (scalarSchemeIso σ).inv) (by
      change pullback.fst f _ ≫ f =
        (pullback.snd f _ ≫ (scalarSchemeIso σ.symm).hom) ≫ _
      rw [Category.assoc, scalarSchemeIso_over]
      exact pullback.condition)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp]
      erw [pullback.lift_fst, pullback.lift_fst]
    · simp only [Category.assoc, Category.id_comp]
      erw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp]
      erw [pullback.lift_fst, pullback.lift_fst]
    · simp only [Category.assoc, Category.id_comp]
      erw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[simp]
lemma geometricFiberIso_hom_fst {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : L ≃ₐ[k] L) :
    (geometricFiberIso f σ).hom ≫ pullback.fst f _ = pullback.fst f _ :=
  pullback.lift_fst _ _ _

@[simp]
lemma geometricFiberIso_hom_snd {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : L ≃ₐ[k] L) :
    (geometricFiberIso f σ).hom ≫ pullback.snd f _ =
      pullback.snd f _ ≫ (scalarSchemeIso σ).hom :=
  pullback.lift_snd _ _ _

end BaseChange

variable (L : Type v) [Field L] [Algebra k L]

/-- The fixed elements of q-power Frobenius in any extension field are
exactly the elements of the finite base field. -/
lemma fixed_by_card_power_iff (z : L) :
    z ^ Fintype.card k = z ↔ ∃ x : k, algebraMap k L x = z := by
  classical
  constructor
  · intro hz
    let P : Polynomial k := Polynomial.X ^ Fintype.card k - Polynomial.X
    have hcard : P.roots.card = P.natDegree := by
      dsimp [P]
      rw [FiniteField.roots_X_pow_card_sub_X,
        FiniteField.X_pow_card_sub_X_natDegree_eq k Fintype.one_lt_card]
      rfl
    have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
      (algebraMap k L).injective hcard
    have hzmem : z ∈ (P.map (algebraMap k L)).roots := by
      apply (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff
        (algebraMap k L).injective).mpr
          (FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card))).mpr
      simpa only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero] using hz
    rw [← hmap, Multiset.mem_map] at hzmem
    obtain ⟨x, _, hx⟩ := hzmem
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

/-- Affine geometric points fixed by Frobenius descend uniquely to
rational points over the finite base field. -/
lemma affine_point_fixed_iff_descends
    (R : Type u) [CommRing R] [Algebra k R] (x : R →ₐ[k] L) :
    (∀ r : R, x r ^ Fintype.card k = x r) ↔
      ∃! y : R →ₐ[k] k, ∀ r : R, algebraMap k L (y r) = x r := by
  constructor
  · intro hx
    choose y hy using fun r => (fixed_by_card_power_iff k L (x r)).mp (hx r)
    let yAlg : R →ₐ[k] k :=
      { toFun := y
        map_zero' := by
          apply (algebraMap k L).injective
          rw [hy, map_zero, map_zero]
        map_one' := by
          apply (algebraMap k L).injective
          rw [hy, map_one, map_one]
        map_add' r s := by
          apply (algebraMap k L).injective
          rw [hy, map_add, map_add, hy, hy]
        map_mul' r s := by
          apply (algebraMap k L).injective
          rw [hy, map_mul, map_mul, hy, hy]
        commutes' r := by
          apply (algebraMap k L).injective
          rw [hy, x.commutes]
          rfl }
    refine ⟨yAlg, hy, ?_⟩
    intro z hz
    ext r
    apply (algebraMap k L).injective
    exact (hz r).trans (hy r).symm
  · rintro ⟨y, hy, _⟩ r
    exact (fixed_by_card_power_iff k L (x r)).mpr ⟨y r, hy r⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry
