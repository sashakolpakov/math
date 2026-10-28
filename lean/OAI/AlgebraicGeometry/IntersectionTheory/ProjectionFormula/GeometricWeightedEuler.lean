import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalWeightedEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GeometricEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

/-! # Geometric Weighted Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricWeightedEuler

noncomputable section

/-! The smooth-stalk Euler expansion in intrinsic geometric dimensions.
All primes and generic lengths belong to the actual scheme stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem rank_eq {K : Type} [Field K] {X : Scheme}
    (f : X ⟶ Spec (.of K)) (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    Affine.SpectrumRank.dimension K Γ(X, U)
      (PrimeSpectrum.comap (X.presheaf.germ U.1 x hx).hom p) =
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f := by
  rw [Affine.GeometricRank.dimension]
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension
    (irreducibleSetEquivPoints.symm (U.2.fromSpec (PrimeSpectrum.comap (X.presheaf.germ U.1 x hx).hom p))) f = _
  rw [Affine.GeometricRank.stalk_image]
  rfl

theorem exists_data {K : Type} [Field K] {X : Scheme}
    (f : X ⟶ Spec (.of K)) (d : ℕ) [SmoothOfRelativeDimension d f]
    (x : X) (M : ModuleCat (X.presheaf.stalk x)) [Module.Finite (X.presheaf.stalk x) M]
    (r : ℕ) (hM : ∀ p ∈ Module.support (X.presheaf.stalk x) M,
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f ≤ r) :
    ∃ F : Finset (PrimeSpectrum (X.presheaf.stalk x)),
      (∀ p ∈ F, p ∈ Module.support (X.presheaf.stalk x) M ∧
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f = r ∧
        FiltrationBaseLength.length (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal) M ≠ ⊤) ∧
      (∀ p, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f = r → p ∉ F →
        FiltrationBaseLength.length (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal) M = 0) ∧
      ∀ (N : ModuleCat (X.presheaf.stalk x)) [Module.Finite (X.presheaf.stalk x) N]
        [HasProjectiveDimensionLE N d] (s : ℕ)
        (_hN : ∀ p ∈ Module.support (X.presheaf.stalk x) N,
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f ≤ s)
        (_heq : r + s = d + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f)
        (_hi : Module.support (X.presheaf.stalk x) M ∩ Module.support (X.presheaf.stalk x) N ⊆
          {IsLocalRing.closedPoint (X.presheaf.stalk x)}),
        Tor.Euler.euler (X.presheaf.stalk x) M N d =
          ∑ p ∈ F, ((FiltrationBaseLength.length (X.presheaf.stalk x)
              (Localization.AtPrime p.asIdeal) M).toNat : ℚ) *
            Tor.Euler.euler (X.presheaf.stalk x) (.of _ (X.presheaf.stalk x ⧸ p.asIdeal)) N d := by
  let : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := f) x
  have hu : U = ⊤ := by
    ext y
    constructor
    · intro _; trivial
    · intro _; exact (Subsingleton.elim (f x) y) ▸ e hx
  subst U
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f V
  let := Stalk.PointAlgebra.scalarAlgebra f x
  let : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, V) :=
    Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra_standardSmooth d f V hstd
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  let : IsScalarTower K Γ(X, V) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun c => ((Stalk.ScalarMaps.germ f V x hx).commutes c).symm
  let q := hV.primeIdealOf ⟨x, hx⟩
  let : IsLocalization q.asIdeal.primeCompl (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hx⟩
  have hδ (p : PrimeSpectrum (X.presheaf.stalk x)) :
      Affine.SpectrumRank.dimension K Γ(X, V)
        (PrimeSpectrum.comap (algebraMap Γ(X, V) (X.presheaf.stalk x)) p) =
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f := rank_eq f ⟨V, hV⟩ x hx p
  obtain ⟨F, hF, hout, he⟩ := ProjectionFormula.Smooth.LocalWeightedEuler.exists_data K Γ(X, V)
    (X.presheaf.stalk x) d q M r (by
      intro p hp
      rw [hδ]
      exact hM p hp)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro p hp
    have h := hF p hp
    rw [hδ] at h
    exact h
  · intro p hp hpF
    apply hout p _ hpF
    rw [hδ]
    exact hp
  · intro N _ _ s hN heq hi
    apply he N s _ _ hi
    · intro p hp
      rw [hδ]
      exact hN p hp
    · rw [Affine.GeometricRank.point_dimension f ⟨V, hV⟩ x hx]
      exact heq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricWeightedEuler
