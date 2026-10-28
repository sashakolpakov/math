import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Embedded

/-! # Embedded Presentation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EmbeddedPresentation.Construction

noncomputable section

/-! A closed-kernel presentation keeps its actual inclusion, monomorphism
and all-test image together for transport through native Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure EmbeddedKernelPresentation {S : Scheme.{u}} (A : Over S)
    (P : ∀ (T : Over S), (T ⟶ A) → Prop) where
  object : Over S
  inclusion : object ⟶ A
  mono : Mono inclusion
  realizes : ∀ (T : Over S) (a : T ⟶ A),
    (∃ h : T ⟶ object, h ≫ inclusion = a) ↔ P T a

variable {k : Type} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] {g : ℕ}
variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable {P : ∀ (T : Over (Spec (.of k))), (T ⟶ A.scheme) → Prop}
variable {P' : ∀ (T : Over (Spec (.of k))), (T ⟶ B.scheme) → Prop}
variable (K : EmbeddedKernelPresentation A.scheme P)
variable (J : EmbeddedKernelPresentation B.scheme P')
variable (e : (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A).scheme ≅ B.scheme)
variable (htransport : Embedded.Construction.FrobeniusKernelTransport A B e P P')

include htransport in
theorem exists_frobeniusKernelPresentationIso :
    ∃ eK : (Over.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).obj K.object ≅ J.object,
      eK.hom ≫ J.inclusion = (Over.pullback
        (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map K.inclusion ≫ e.hom :=
  Embedded.Construction.exists_frobeniusEmbeddedKernelIso A B K.inclusion J.inclusion K.mono J.mono
    e P P' K.realizes J.realizes htransport

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EmbeddedPresentation.Construction
