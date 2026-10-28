import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientFiberPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor

/-! # Ambient Polynomial Functor -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientPolynomialFunctor.Core

noncomputable section

/-! The exact polynomial Hilbert functor in a closed projective ambient
scheme is naturally the intersection of the ambient polynomial functor
with the scheme-theoretic containment condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) [IsClosedImmersion j.left]
variable (B : Has.Core.ProjectivePresentation Y) (P : Polynomial ℚ)

def closedAmbientPolynomialSubfunctor : Subfunctor (Hilbert.Functor.familyFunctor Y) :=
  Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor B P ⊓ Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus j

theorem closedAmbientPolynomialSubfunctor_mem {T : Over S} (F : Hilbert.Functor.Family Y T) :
    F ∈ (closedAmbientPolynomialSubfunctor j B P).obj (.op T) ↔
      Has.Core.HasFiberHilbertPolynomial B F P ∧ (Hilbert.ClosedAmbientMap.ambientEmbedding j T).ker ≤ F.val := by
  change (Has.Core.HasFiberHilbertPolynomial B F P ∧ F ∈ (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus j).obj (.op T)) ↔ _
  rw [Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus_mem]

def closedAmbientPolynomialTransformation : (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (B.precompose j) P).toFunctor ⟶
    (closedAmbientPolynomialSubfunctor j B P).toFunctor where
  app T := ↾fun F => ⟨Hilbert.ClosedAmbientMap.pushforwardFamily j F.val,
    (closedAmbientPolynomialSubfunctor_mem j B P _).mpr
      ⟨(AmbientFiberPolynomial.Core.hasFiberHilbertPolynomial_pushforward_iff j B F.val P).mpr F.property,
        (Hilbert.ClosedAmbientRange.pushforwardFamily_range_iff j _).mp ⟨F.val, rfl⟩⟩⟩
  naturality T U a := by
    apply ConcreteCategory.hom_ext
    intro F
    exact Subtype.ext (Hilbert.ClosedAmbientNaturality.pushforwardFamily_baseChange j a.unop F.val)

instance closedAmbientPolynomialTransformation_isIso :
    IsIso (closedAmbientPolynomialTransformation j B P) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro T
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro F G h
    apply Subtype.ext
    exact Hilbert.ClosedAmbientNaturality.pushforwardFamily_injective j T.unop (congrArg Subtype.val h)
  · intro F
    obtain ⟨hP, hF⟩ := (closedAmbientPolynomialSubfunctor_mem j B P F.val).mp F.property
    obtain ⟨G, hG⟩ := (Hilbert.ClosedAmbientRange.pushforwardFamily_range_iff j F.val).mpr hF
    have hGP : Has.Core.HasFiberHilbertPolynomial (B.precompose j) G P :=
      (AmbientFiberPolynomial.Core.hasFiberHilbertPolynomial_pushforward_iff j B G P).mp (hG.symm ▸ hP)
    exact ⟨⟨G, hGP⟩, Subtype.ext hG⟩

def closedAmbientPolynomialEquivalence : (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (B.precompose j) P).toFunctor ≅
    (closedAmbientPolynomialSubfunctor j B P).toFunctor := by
  let t := closedAmbientPolynomialTransformation j B P
  let e := asIso t
  exact e

theorem closedAmbientPolynomialEquivalence_inclusion :
    (closedAmbientPolynomialEquivalence j B P).hom ≫ (closedAmbientPolynomialSubfunctor j B P).ι =
      (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (B.precompose j) P).ι ≫ Hilbert.ClosedAmbientNaturality.closedAmbientTransformation j := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientPolynomialFunctor.Core
