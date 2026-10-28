import OAI.AlgebraicGeometry.SheafCohomology.Projective.HilbertDimension
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateBundleIso
import OAI.AlgebraicGeometry.SheafCohomology.Projective.KrullTranscendenceDimension

/-! # Intrinsic Degree -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicDegree

noncomputable section

/-! Projective section polynomials have intrinsic degree, independently of the chosen coordinate. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
namespace Dimension

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem closedProjective_Hilbert_intrinsicDegree
    {K R : Type u} [Field K] [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsIntegral X] (ρ : X ⟶ Spec (.of K)) [LocallyOfFiniteType ρ]
    {σ : Type} [Fintype σ] [LinearOrder σ]
    (hfield : IsField Γ(Spec (.of R), ⊤))
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (j : σ) (P : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj
            (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))) : ℚ) =
        P.eval (n : ℚ)) :
    P.natDegree = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ ∧ 0 < P.leadingCoeff := by
  let := hfield.toField
  let x : X := Classical.choice inferInstance
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show f x ∈ ⨆ k : σ, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k by
      rw [MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]; trivial)
  have : Nonempty (f ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen k) := ⟨⟨x, hk⟩⟩
  have hQ (n : ℕ) (hn : b ≤ n) :
      (Module.finrank Γ(Spec (.of R), ⊤)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
          ((Scheme.Modules.pullback f).obj
            (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) k n))) : ℚ) =
        P.eval (n : ℚ) := by
    let e := (Scheme.Modules.pullback f).mapIso (CoordinateBundleIso.Dimension.projectiveTwistCoordinateIso (R := R) j k n)
    have he := ((AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso e).toLinearEquiv.finrank_eq
    exact (congrArg (fun d : ℕ => (d : ℚ)) he).symm.trans (hP n hn)
  have hd := (HilbertDimension.Dimension.closedProjective_Hilbert_natDegree hfield f k P b hQ).trans
    (KrullTranscendenceDimension.Dimension.affine_chart_krullDimension ρ _ ((MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) k).preimage f))
  exact ⟨by exact_mod_cast hd, HilbertDimension.Dimension.closedProjective_Hilbert_leadingCoeff_pos hfield f k P b hQ⟩

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicDegree
