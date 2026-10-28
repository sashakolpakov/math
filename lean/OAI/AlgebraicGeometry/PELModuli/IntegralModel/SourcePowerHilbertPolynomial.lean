import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ProjectiveHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.IntrinsicCoordinateIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps

/-! # Source Power Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SourcePowerHilbertPolynomial

noncomputable section

/-! Choose the graph polynomial from the source polarization alone.
Scaling the twist exponent scales the polynomial variable; no source CM
action or initial Segre presentation is needed for this choice. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_sourcePower_sections_polynomial
    {k : Type u} [Field k] {X : Scheme.{u}} {n : ℕ}
    (f : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k n)) [IsClosedImmersion f]
    (π : X ⟶ Spec (.of k)) (hf : f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k) = π)
    (j : Fin (n + 1)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (hL : ∀ m, Nonempty ((Scheme.Modules.pullback f).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) j m) ≅ (L.tensorPower m).sheaf))
    (r : ℕ) (hr : 0 < r) :
    ∃ P : Polynomial ℚ, ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      (Module.finrank Γ(Spec (.of k), ⊤)
        ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj (L.tensorPower (r * m)).sheaf) : ℚ) = P.eval (m : ℚ) := by
  classical
  have hfield : IsField Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
  obtain ⟨Q, _, b, hb⟩ := Projective.HilbertSections.PolarizationEmbedding.nativeTwistSections_eventuallyPolynomial f j hfield
  refine ⟨Q.comp (Polynomial.C (r : ℚ) * Polynomial.X), b, fun m hm => ?_⟩
  have hbound : b ≤ r * m := hm.trans (Nat.le_mul_of_pos_left m hr)
  have hdim := (Fixed.ProjectiveHilbertPolynomial.PolarizationEmbedding.nativeTwistSectionsFixedEquiv f π hf j (r * m) (L.tensorPower (r * m)).sheaf
    (Classical.choice (hL (r * m)))).finrank_eq
  rw [← hdim, hb (r * m) hbound]
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Nat.cast_mul]

theorem e34HilbertPolynomial_of_eventual_sections
    {k : Type u} [Field k] {X : Scheme.{u}} {n : ℕ}
    (f : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k n)) [IsClosedImmersion f]
    (π : X ⟶ Spec (.of k)) (hf : f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k) = π)
    (j : Fin (n + 1)) (L : ℕ → X.Modules)
    (hL : ∀ m, Nonempty ((Scheme.Modules.pullback f).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) j m) ≅ L m))
    (P : Polynomial ℚ) (hP : ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      (Module.finrank Γ(Spec (.of k), ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj (L m)) : ℚ) = P.eval (m : ℚ)) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker).toIdeal P := by
  classical
  apply (Presentations.IntrinsicCoordinateIdeal.PolarizationEmbedding.native_hasHilbertPolynomial_iff_e34 f P).mp
  obtain ⟨b, hb⟩ := Projective.HilbertSections.PolarizationEmbedding.eventually_nativeHilbertFunction_eq_sections f j
  obtain ⟨c, hc⟩ := hP
  refine ⟨max b c, fun m hm => ?_⟩
  rw [hb m ((le_max_left b c).trans hm),
    (Fixed.ProjectiveHilbertPolynomial.PolarizationEmbedding.nativeTwistSectionsFixedEquiv f π hf j m (L m) (Classical.choice (hL m))).finrank_eq]
  exact hc m ((le_max_right b c).trans hm)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SourcePowerHilbertPolynomial
