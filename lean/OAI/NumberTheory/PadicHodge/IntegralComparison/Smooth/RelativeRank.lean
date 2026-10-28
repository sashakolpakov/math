import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedSections
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Relative Rank -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RelativeRank

noncomputable section

/-! Smooth relative dimension computes the rank of the actual relative
differential module on affine sections and closed-subscheme quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

theorem locally_standard_smooth_rank (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (p : PrimeSpectrum A) : Module.rankAtStalk Ω[A⁄R] p = n := by
  classical
  obtain ⟨s, hs, hloc⟩ := h
  have hex : ∃ r ∈ s, r ∉ p.asIdeal := by
    by_contra hn
    have hle : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr (by
      intro r hr
      by_contra hnr
      exact hn ⟨r, hr, hnr⟩)
    rw [hs] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨r, hr, hpr⟩ := hex
  let T := Localization.Away r
  have hst : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
    have H := hloc r hr
    rw [← IsScalarTower.algebraMap_eq R A T,
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at H
    exact H
  let := hst
  have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A T)) := by
    rw [PrimeSpectrum.localization_away_comap_range T r]
    exact hpr
  obtain ⟨q, hq⟩ := hmem
  let : Nontrivial T := q.nontrivial
  let : Algebra.IsStandardSmooth R T := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let : Algebra.FormallyEtale A T := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  have H := Module.rankAtStalk_isBaseChange (KaehlerDifferential.isBaseChange_of_formallyEtale R A T) q
  rw [hq] at H
  have hn : Module.finrank T Ω[T⁄R] = n := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := T) n)
  exact H.symm.trans ((congrFun (Module.rankAtStalk_eq_finrank_of_free (R := T) (M := Ω[T⁄R])) q).trans hn)

theorem locally_standard_smooth_of_equiv {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (n : ℕ) (e : A ≃ₐ[R] B)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R B) := by
  have H := (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left (algebraMap R A) e.toRingEquiv h
  have he : e.toRingEquiv.toRingHom.comp (algebraMap R A) = algebraMap R B := by
    ext r
    exact e.commutes r
  exact he ▸ H

variable {X Y S : Scheme.{u}} [IsAffine S]

theorem sections_locally_standard_smooth (π : Y ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n π] (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := ClosedSections.algebra π U
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap Γ(S, ⊤) Γ(Y, U)) := by
  let := ClosedSections.algebra π U
  exact HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) π inferInstance
    ⟨⊤, isAffineOpen_top S⟩ ⟨U, hU⟩ le_top

theorem sections_rank (π : Y ⟶ S) (n : ℕ) [SmoothOfRelativeDimension n π]
    (U : Y.Opens) (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(Y, U)) :
    letI := ClosedSections.algebra π U
    Module.rankAtStalk Ω[Γ(Y, U)⁄Γ(S, ⊤)] p = n := by
  let := ClosedSections.algebra π U
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have := ClosedSections.smooth_sections π U hU
  exact locally_standard_smooth_rank _ _ n (sections_locally_standard_smooth π n U hU) p

theorem quotient_rank (f : X ⟶ Y) [IsClosedImmersion f] (π : Y ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n (f ≫ π)] (U : Y.Opens) (hU : IsAffineOpen U)
    (p : PrimeSpectrum (Γ(Y, U) ⧸ f.ker.ideal ⟨U, hU⟩)) :
    letI := ClosedSections.algebra π U
    Module.rankAtStalk Ω[Γ(Y, U) ⧸ f.ker.ideal ⟨U, hU⟩⁄Γ(S, ⊤)] p = n := by
  let := ClosedSections.algebra π U
  let := ClosedSections.algebra (f ≫ π) (f ⁻¹ᵁ U)
  have : Smooth (f ≫ π) := SmoothOfRelativeDimension.smooth n (f ≫ π)
  have := ClosedSections.smooth_quotient f π U hU
  have h := locally_standard_smooth_of_equiv n
    (ClosedSections.quotientEquiv f π U hU).symm
    (sections_locally_standard_smooth (f ≫ π) n (f ⁻¹ᵁ U) (hU.preimage f))
  exact locally_standard_smooth_rank _ _ n h p

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RelativeRank
