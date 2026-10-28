import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentDegree
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Laurent Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentCoordinates.ProjectiveCech

noncomputable section

/-! Laurent coordinates in one common exponent space for all projective charts. -/

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]

def allowedExponents (s : Finset σ) : Set (σ → ℤ) := {a | ∀ i ∉ s, 0 ≤ a i}

def chartCoordinateEquiv (s : Finset σ) : LaurentMonomials.ProjectiveCech.ChartLocalization R s ≃ₗ[R]
    Finsupp.supported R R (allowedExponents s) :=
  (LaurentBasis.ProjectiveCech.laurentBasis R s).repr.trans (Finsupp.supportedEquivFinsupp (R := R) (allowedExponents s)).symm

def chartCoordinates (s : Finset σ) : LaurentMonomials.ProjectiveCech.ChartLocalization R s →ₗ[R] (σ → ℤ) →₀ R :=
  (Finsupp.supported R R (allowedExponents s)).subtype.comp (chartCoordinateEquiv R s).toLinearMap

theorem chartCoordinates_apply (s : Finset σ) (x : LaurentMonomials.ProjectiveCech.ChartLocalization R s) :
    chartCoordinates R s x = ((LaurentBasis.ProjectiveCech.laurentBasis R s).repr x).extendDomain := by
  let : DecidablePred (fun a => a ∈ allowedExponents s) :=
    fun a => inferInstanceAs (Decidable (∀ i ∉ s, 0 ≤ a i))
  exact Finsupp.supportedEquivFinsupp_symm_apply_coe (R := R)
    (allowedExponents s) ((LaurentBasis.ProjectiveCech.laurentBasis R s).repr x)

theorem chartCoordinates_injective (s : Finset σ) : Function.Injective (chartCoordinates R s) :=
  Subtype.val_injective.comp (chartCoordinateEquiv R s).injective

theorem chartCoordinates_support (s : Finset σ) (x : LaurentMonomials.ProjectiveCech.ChartLocalization R s) :
    ∀ a ∈ (chartCoordinates R s x).support, a ∈ allowedExponents s :=
  (chartCoordinateEquiv R s x).property

theorem chartCoordinates_of_not_allowed (s : Finset σ) (x : LaurentMonomials.ProjectiveCech.ChartLocalization R s)
    (a : σ → ℤ) (ha : a ∉ allowedExponents s) : chartCoordinates R s x a = 0 := by
  by_contra hn
  exact ha (chartCoordinates_support R s x a (Finsupp.mem_support_iff.mpr hn))

theorem chartCoordinates_laurentMonomial (s : Finset σ) (a : LaurentExponents.ProjectiveCech.LaurentExponent s) :
    chartCoordinates R s (LaurentMonomials.ProjectiveCech.laurentMonomial R a) = Finsupp.single a.val 1 := by
  classical
  rw [chartCoordinates_apply, ← LaurentBasis.ProjectiveCech.laurentBasis_apply R s a, Module.Basis.repr_self,
    Finsupp.extendDomain_single]

def chartOfCoordinates (s : Finset σ) : ((σ → ℤ) →₀ R) →ₗ[R] LaurentMonomials.ProjectiveCech.ChartLocalization R s :=
  (LaurentBasis.ProjectiveCech.laurentBasis R s).repr.symm.toLinearMap.comp (Finsupp.lsubtypeDomain (allowedExponents s))

theorem chartOfCoordinates_coordinates (s : Finset σ) (x : LaurentMonomials.ProjectiveCech.ChartLocalization R s) :
    chartOfCoordinates R s (chartCoordinates R s x) = x := by
  rw [chartCoordinates_apply]
  change (LaurentBasis.ProjectiveCech.laurentBasis R s).repr.symm (Finsupp.subtypeDomain _
    ((LaurentBasis.ProjectiveCech.laurentBasis R s).repr x).extendDomain) = x
  rw [Finsupp.subtypeDomain_extendDomain, LinearEquiv.symm_apply_apply]

theorem chartCoordinates_ofCoordinates (s : Finset σ) (f : (σ → ℤ) →₀ R)
    (hf : ∀ a ∈ f.support, a ∈ allowedExponents s) :
    chartCoordinates R s (chartOfCoordinates R s f) = f := by
  rw [chartCoordinates_apply]
  change ((LaurentBasis.ProjectiveCech.laurentBasis R s).repr ((LaurentBasis.ProjectiveCech.laurentBasis R s).repr.symm
    (Finsupp.subtypeDomain _ f))).extendDomain = f
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.extendDomain_subtypeDomain f hf

theorem chartCoordinates_restriction {s t : Finset σ} (h : s ⊆ t) (x : LaurentMonomials.ProjectiveCech.ChartLocalization R s) :
    chartCoordinates R t (LaurentRestriction.ProjectiveCech.chartRestriction R h x) = chartCoordinates R s x := by
  have he : (chartCoordinates R t).comp (LaurentRestriction.ProjectiveCech.chartRestriction R h).toLinearMap = chartCoordinates R s := by
    apply (LaurentBasis.ProjectiveCech.laurentBasis R s).ext
    intro a
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LaurentBasis.ProjectiveCech.laurentBasis_apply,
      LaurentRestriction.ProjectiveCech.chartRestriction_laurentMonomial, chartCoordinates_laurentMonomial]
    rfl
  exact LinearMap.congr_fun he x

theorem chartCoordinates_degree (s : Finset σ) (d : ℤ) (x : LaurentMonomials.ProjectiveCech.ChartLocalization R s)
    (hx : x ∈ LaurentDegree.ProjectiveCech.laurentDegreeSubmodule R s d) (a : σ → ℤ) (ha : LaurentDegree.ProjectiveCech.exponentDegree a ≠ d) :
    chartCoordinates R s x a = 0 := by
  classical
  rw [chartCoordinates_apply, Finsupp.extendDomain_apply]
  split_ifs with h
  · exact (LaurentDegree.ProjectiveCech.mem_laurentDegreeSubmodule_iff R s d x).mp hx ⟨a, h⟩ ha
  · rfl

theorem chartOfCoordinates_degree (s : Finset σ) (d : ℤ) (f : (σ → ℤ) →₀ R)
    (hf : ∀ a, LaurentDegree.ProjectiveCech.exponentDegree a ≠ d → f a = 0) :
    chartOfCoordinates R s f ∈ LaurentDegree.ProjectiveCech.laurentDegreeSubmodule R s d := by
  rw [LaurentDegree.ProjectiveCech.mem_laurentDegreeSubmodule_iff]
  intro a ha
  change (LaurentBasis.ProjectiveCech.laurentBasis R s).repr ((LaurentBasis.ProjectiveCech.laurentBasis R s).repr.symm
    (Finsupp.subtypeDomain _ f)) a = 0
  rw [LinearEquiv.apply_symm_apply, Finsupp.subtypeDomain_apply]
  exact hf a.val ha

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentCoordinates.ProjectiveCech
