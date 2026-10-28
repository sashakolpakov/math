import Mathlib.LinearAlgebra.Isomorphisms
import OAI.NumberTheory.PadicHodge.IntegralComparison.BaseChangeQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormScalarExtension

/-! # Forms Exactness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormsExactness

noncomputable section

/-! The actual form pullback to a base quotient is surjective with exactly the base-ideal kernel. -/

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A] [LinearOrder σ]
  (I : Ideal R) (x : σ → A) (b : Module.Basis σ A (KaehlerDifferential R A))
  (hb : ∀ i, b i = KaehlerDifferential.D R A (x i)) (m : ℕ)

local notation "B" => A ⧸ I.map (algebraMap R A)
local notation "M" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m
local notation "N" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B m
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars.Ordinary.map R A B m

def equiv : (M ⧸ (I.map (algebraMap R A) • ⊤ : Submodule A M)) ≃ₗ[A] N :=
  BaseChangeQuotient.equiv A (I.map (algebraMap R A)) M N f
    (FormScalarExtension.isBaseChange R A σ I x b hb m)

theorem equiv_mk (ω : M) : equiv R A σ I x b hb m (Submodule.Quotient.mk ω) = f ω :=
  BaseChangeQuotient.equiv_mk A (I.map (algebraMap R A)) M N f
    (FormScalarExtension.isBaseChange R A σ I x b hb m) ω

include σ x b hb in
theorem surjective : Function.Surjective f :=
  BaseChangeQuotient.surjective A (I.map (algebraMap R A)) M N f
    (FormScalarExtension.isBaseChange R A σ I x b hb m)

include σ x b hb in
theorem kernel : LinearMap.ker f = I.map (algebraMap R A) • ⊤ :=
  BaseChangeQuotient.kernel A (I.map (algebraMap R A)) M N f
    (FormScalarExtension.isBaseChange R A σ I x b hb m)

include σ x b hb in
theorem kernel_restrictScalars : LinearMap.ker ((f).restrictScalars R) = I • ⊤ := by
  change (LinearMap.ker f).restrictScalars R = _
  rw [kernel R A σ I x b hb m, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

def scalarEquiv : (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R] N :=
  (Submodule.quotEquivOfEq _ _ (kernel_restrictScalars R A σ I x b hb m).symm).trans
    (((f).restrictScalars R).quotKerEquivOfSurjective (surjective R A σ I x b hb m))

theorem scalarEquiv_mk (ω : M) : scalarEquiv R A σ I x b hb m (Submodule.Quotient.mk ω) = f ω := by
  simp only [scalarEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk ((f).restrictScalars R)
    (surjective R A σ I x b hb m) ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormsExactness
