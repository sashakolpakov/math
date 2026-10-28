import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EmbeddedBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport

/-! # Embedded -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Embedded.Construction

noncomputable section

section

/-! Reconstruct embedded kernel pullbacks using the same native
Frobenius abelian target and point identification as the pairing theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] {g : ℕ}
variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable {H J : Over (Spec (.of k))} (i : H ⟶ A.scheme) (j : J ⟶ B.scheme)
variable (hi : Mono i) (hj : Mono j)
variable (e : (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A).scheme ≅ B.scheme)
variable (P : ∀ (T : Over (Spec (.of k))), (T ⟶ A.scheme) → Prop)
variable (P' : ∀ (T : Over (Spec (.of k))), (T ⟶ B.scheme) → Prop)
variable (hP : ∀ (T : Over (Spec (.of k))) (a : T ⟶ A.scheme),
  (∃ h : T ⟶ H, h ≫ i = a) ↔ P T a)
variable (hP' : ∀ (T : Over (Spec (.of k))) (a : T ⟶ B.scheme),
  (∃ h : T ⟶ J, h ≫ j = a) ↔ P' T a)
variable (htransport : ∀ (T : Over (Spec (.of k)))
    (a : T ⟶ (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A).scheme),
  P' T (a ≫ e.hom) ↔ P
    ((Over.map (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).obj T)
    (A.baseChangePointsMulEquiv
      (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))) T a))

include hi hj hP hP' htransport in
theorem exists_frobeniusEmbeddedKernelIso :
    ∃ eH : (Over.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).obj H ≅ J,
      eH.hom ≫ j = (Over.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map i ≫ e.hom := by
  have : Mono i := hi
  have : Mono j := hj
  exact EmbeddedBaseChange.Construction.exists_embeddedKernelBaseChangeIso _ i j e P P' hP hP' htransport

end

/-! The exact all-test predicate transport across the specified native
Frobenius comparison, exposed without expanding full PEL point data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] {g : ℕ}

def FrobeniusKernelTransport
    (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (e : (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A).scheme ≅ B.scheme)
    (P : ∀ (T : Over (Spec (.of k))), (T ⟶ A.scheme) → Prop)
    (P' : ∀ (T : Over (Spec (.of k))), (T ⟶ B.scheme) → Prop) : Prop :=
  ∀ (T : Over (Spec (.of k))) (a : T ⟶ (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A).scheme),
    P' T (a ≫ e.hom) ↔ P
      ((Over.map (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).obj T)
      (A.baseChangePointsMulEquiv
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))) T a)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Embedded.Construction
