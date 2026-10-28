import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Embedded
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessBaseChange

/-! # Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Group.Construction

noncomputable section

/-! Predicate transport reconstructs the kernel isomorphism in the
literal base-changed group representation of a full quotient witness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] {g : ℕ}
  (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (H J : Grp (Over (Spec (.of k)))) (i : H.X ⟶ A.scheme) (j : J.X ⟶ B.scheme)
  (hi : Mono i) (hj : Mono j)
  (e : (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A).scheme ≅ B.scheme)
  (P : ∀ (T : Over (Spec (.of k))), (T ⟶ A.scheme) → Prop)
  (P' : ∀ (T : Over (Spec (.of k))), (T ⟶ B.scheme) → Prop)
  (hP : ∀ (T : Over (Spec (.of k))) (a : T ⟶ A.scheme),
    (∃ h : T ⟶ H.X, h ≫ i = a) ↔ P T a)
  (hP' : ∀ (T : Over (Spec (.of k))) (a : T ⟶ B.scheme),
    (∃ h : T ⟶ J.X, h ≫ j = a) ↔ P' T a)
  (hci : IsClosedImmersion i.left) (hcj : IsClosedImmersion j.left)
  (htransport : Embedded.Construction.FrobeniusKernelTransport A B e P P')

include hi hj hP hP' htransport in
theorem exists_frobeniusGroupKernelIso :
    ∃ eH : (QuotientWitnessBaseChange.Construction.baseChangedKernelGroup
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))) H).X ≅ J.X,
      eH.hom ≫ j = (Over.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map i ≫ e.hom :=
  Embedded.Construction.exists_frobeniusEmbeddedKernelIso A B i j hi hj e P P' hP hP' htransport

include hci hcj hP hP' htransport in
theorem exists_frobeniusGroupKernelIso_of_closed :
    ∃ eH : (QuotientWitnessBaseChange.Construction.baseChangedKernelGroup
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))) H).X ≅ J.X,
      eH.hom ≫ j = (Over.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map i ≫ e.hom := by
  have : IsClosedImmersion i.left := hci
  have : IsClosedImmersion j.left := hcj
  exact exists_frobeniusGroupKernelIso A B H J i j
    (Over.mono_of_mono_left i) (Over.mono_of_mono_left j) e P P' hP hP' htransport

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Group.Construction
