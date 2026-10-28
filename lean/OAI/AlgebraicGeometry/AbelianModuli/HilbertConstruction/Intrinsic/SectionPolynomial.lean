import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LineBundleSections
import Mathlib.Algebra.Polynomial.Roots

/-! # Section Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The intrinsic Hilbert polynomial is the eventual dimension of actual global sections of tensor powers, with finite-dimensionality required explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

def Line.Bundles.LineBundle.HasSectionHilbertPolynomial (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) (P : Polynomial ℚ) : Prop :=
  ∃ b : ℕ, ∀ d : ℕ, b ≤ d →
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower d).sheaf) ∧
      P.eval (d : ℚ) = (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower d).sheaf) : ℚ)

theorem Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sectionIso
    {Y : Scheme.{u}} (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K))
    (L : Line.Bundles.LineBundle X) (M : Line.Bundles.LineBundle Y) (P : Polynomial ℚ)
    (e : ∀ d : ℕ, (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower d).sheaf ≃ₗ[K]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor q).obj (M.tensorPower d).sheaf) :
    L.HasSectionHilbertPolynomial p P ↔ M.HasSectionHilbertPolynomial q P := by
  constructor
  · rintro ⟨b, h⟩
    refine ⟨b, fun d hd => ?_⟩
    obtain ⟨hf, he⟩ := h d hd
    have := hf
    exact ⟨Module.Finite.equiv (e d), he.trans (congrArg (fun n : ℕ => (n : ℚ)) (e d).finrank_eq)⟩
  · rintro ⟨b, h⟩
    refine ⟨b, fun d hd => ?_⟩
    obtain ⟨hf, he⟩ := h d hd
    have := hf
    exact ⟨Module.Finite.equiv (e d).symm, he.trans (congrArg (fun n : ℕ => (n : ℚ)) (e d).symm.finrank_eq)⟩

theorem Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_overIso
    {A B : Over (Spec (.of K))} (f : A ≅ B)
    (L : Line.Bundles.LineBundle B.left) (M : Line.Bundles.LineBundle A.left) (e : (L.pullback f.hom.left).sheaf ≅ M.sheaf)
    (P : Polynomial ℚ) :
    L.HasSectionHilbertPolynomial B.hom P ↔ M.HasSectionHilbertPolynomial A.hom P :=
  Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sectionIso B.hom A.hom L M P
    (Intrinsic.LineBundleSections.lineBundlePowerSectionsOverIso f L M e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
