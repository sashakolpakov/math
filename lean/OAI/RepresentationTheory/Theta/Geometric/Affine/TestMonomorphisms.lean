import OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismLocalLifts
import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientPoints

/-! # Test Monomorphisms -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.TestMonomorphisms

noncomputable section

/-! Equality of the affine test points of two subobjects gives an actual
scheme isomorphism. This recognizes a locally constructed equation locus. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismLocalLifts.Construction

universe u

theorem mono_over_hom_ext {S : Scheme.{u}} (M T : Over S) [Mono M.hom]
    (p q : T ⟶ M) : p = q := by
  apply Over.OverMorphism.ext
  exact (cancel_mono M.hom).mp (p.w.trans q.w.symm)

theorem mono_hasLift_of_affineTests {S : Scheme.{u}} (M N : Over S) [Mono N.hom]
    (h : ∀ (T : Over S) [IsAffine T.left], Nonempty (T ⟶ M) → Nonempty (T ⟶ N)) :
    Nonempty (M ⟶ N) := by
  apply AlgebraicGeometry.FormalGeometry.Completion.MonomorphismLocalLifts.Construction.mono_hasLift_of_openCover N M M.left.affineCover
  intro i
  have : IsAffine (Over.mk (M.left.affineCover.f i ≫ M.hom)).left :=
    inferInstanceAs (IsAffine (M.left.affineCover.X i))
  exact h _ ⟨Over.homMk (M.left.affineCover.f i) rfl⟩

def monoIsoOfAffineTests {S : Scheme.{u}} (M N : Over S) [Mono M.hom] [Mono N.hom]
    (h : ∀ (T : Over S) [IsAffine T.left], Nonempty (T ⟶ M) ↔ Nonempty (T ⟶ N)) :
    M ≅ N where
  hom := Classical.choice (mono_hasLift_of_affineTests M N (fun T _ => (h T).mp))
  inv := Classical.choice (mono_hasLift_of_affineTests N M (fun T _ => (h T).mpr))
  hom_inv_id := mono_over_hom_ext M M _ _
  inv_hom_id := mono_over_hom_ext N N _ _

def monoAffineQuotientIso {S : Scheme.{u}} [IsAffine S] (M : Over S) [Mono M.hom]
    (I : Ideal Γ(S, ⊤))
    (h : ∀ (T : Over S) [IsAffine T.left],
      Nonempty (T ⟶ M) ↔ I ≤ RingHom.ker T.hom.appTop.hom) :
    M ≅ QuotientPoints.affineQuotientScheme S I :=
  monoIsoOfAffineTests M (QuotientPoints.affineQuotientScheme S I)
    (fun T _ => (h T).trans (QuotientPoints.affineQuotientScheme_hasLift_iff S I T).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.TestMonomorphisms
