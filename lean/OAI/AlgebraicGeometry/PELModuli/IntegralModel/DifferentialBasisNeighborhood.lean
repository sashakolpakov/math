import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEtaleDifferentials
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-! # Differential Basis Neighborhood -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DifferentialBasisNeighborhood

noncomputable section

/-! A flat finitely presented module of differentials has a local
basis made from differentials of actual elements of the original algebra. -/

open TensorProduct KaehlerDifferential _root_.Module

theorem exists_differential_basis_neighborhood
    (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat A Ω[A⁄R]]
    (p : Ideal A) [p.IsPrime] :
    ∃ g : A, g ∉ p ∧ ∃ (ι : Type) (_ : Finite ι) (a : ι → A)
      (b : Basis ι (Localization.Away g) Ω[Localization.Away g⁄R]),
      ∀ i, b i = D R (Localization.Away g) (algebraMap A (Localization.Away g) (a i)) := by
  let Ap := Localization.AtPrime p
  have : Algebra.FormallyEtale A Ap := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have : Module.Flat Ap Ω[Ap⁄R] := Module.Flat.of_linearEquiv
    (tensorKaehlerEquivOfFormallyEtale R A Ap).symm
  have : Module.FinitePresentation Ap Ω[Ap⁄R] := Module.FinitePresentation.of_equiv
    (tensorKaehlerEquivOfFormallyEtale R A Ap)
  obtain ⟨ι, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R A Ap p.primeCompl)
  let e : (ι →₀ A) →ₗ[A] Ω[A⁄R] := Finsupp.linearCombination A fun i => D R A (a i)
  let l₁ : (ι →₀ A) →ₗ[A] (ι →₀ Ap) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A Ap)
  let l₂ : Ω[A⁄R] →ₗ[A] Ω[Ap⁄R] := map R R A Ap
  let eₚ : (ι →₀ Ap) →ₗ[Ap] Ω[Ap⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ Ap e
  have heₚ : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e (l₁ (Finsupp.single i 1))
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb]
  have : Finite ι := Module.Finite.finite_basis b
  have heₚbij : Function.Bijective eₚ := heₚ.symm ▸ b.repr.symm.bijective
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂
    heₚbij
  let l₁g : (ι →₀ A) →ₗ[A] (ι →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A _)
  let l₂g : Ω[A⁄R] →ₗ[A] Ω[Localization.Away g⁄R] := map R R A (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁g l₂g] at h
  let eg : (ι →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁g l₂g (Localization.Away g) e
  let bg := Basis.ofRepr (LinearEquiv.ofBijective eg h).symm
  refine ⟨g, hg, ι, inferInstance, a, bg, ?_⟩
  intro i
  change eg (Finsupp.single i 1) = _
  trans IsLocalizedModule.map (Submonoid.powers g) l₁g l₂g e (l₁g (Finsupp.single i 1))
  · simp [eg, -IsLocalizedModule.map_apply, l₁g]
  · simp [l₂g, e]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DifferentialBasisNeighborhood
