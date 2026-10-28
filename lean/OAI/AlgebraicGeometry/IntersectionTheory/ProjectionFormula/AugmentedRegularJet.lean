import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Augmented Regular Jet -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedRegularJet

noncomputable section

/-! The first-order algebra of a regular local ring at a rational
point has dimension one greater than the local dimension. -/

set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent

universe u v

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]
  (ε : R →ₐ[K] K)

theorem surjective : Function.Surjective ε :=
  fun c => ⟨algebraMap K R c, ε.commutes c⟩

theorem ideal_eq [IsLocalRing R] : AugmentedCotangent.ideal ε = IsLocalRing.maximalIdeal R :=
  IsLocalRing.ker_eq_maximalIdeal ε.toRingHom (surjective ε)

def residueEquiv : (R ⧸ AugmentedCotangent.ideal ε) ≃ₐ[K] K :=
  Ideal.quotientKerAlgEquivOfSurjective (surjective ε)

instance cotangent_tower : IsScalarTower K (R ⧸ AugmentedCotangent.ideal ε) (AugmentedCotangent.ideal ε).Cotangent :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (algebraMap R (R ⧸ AugmentedCotangent.ideal ε) (algebraMap K R c)) • x = c • x
    rw [IsScalarTower.algebraMap_smul (R ⧸ AugmentedCotangent.ideal ε), IsScalarTower.algebraMap_smul R]

theorem finite_cotangent [IsNoetherianRing R] : Module.Finite K (AugmentedCotangent.ideal ε).Cotangent := by
  let : Module.Finite R (AugmentedCotangent.ideal ε).Cotangent :=
    Module.Finite.of_surjective (AugmentedCotangent.ideal ε).toCotangent (AugmentedCotangent.ideal ε).toCotangent_surjective
  let : Module.Finite K (R ⧸ AugmentedCotangent.ideal ε) :=
    Module.Finite.of_injective (residueEquiv ε).toLinearMap (residueEquiv ε).injective
  let : Module.Finite (R ⧸ AugmentedCotangent.ideal ε) (AugmentedCotangent.ideal ε).Cotangent :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact Module.Finite.trans (R ⧸ AugmentedCotangent.ideal ε) (AugmentedCotangent.ideal ε).Cotangent

theorem cotangent_dimension [IsRegularLocalRing R] :
    (Module.finrank K (AugmentedCotangent.ideal ε).Cotangent : WithBot ℕ∞) = ringKrullDim R := by
  let : (AugmentedCotangent.ideal ε).IsMaximal := by rw [ideal_eq]; infer_instance
  let : Field (R ⧸ AugmentedCotangent.ideal ε) := Ideal.Quotient.field (AugmentedCotangent.ideal ε)
  let : Module.Finite K (R ⧸ AugmentedCotangent.ideal ε) :=
    Module.Finite.of_injective (residueEquiv ε).toLinearMap (residueEquiv ε).injective
  have hf : Module.finrank K (R ⧸ AugmentedCotangent.ideal ε) = 1 := by
    rw [(residueEquiv ε).toLinearEquiv.finrank_eq, Module.finrank_self]
  have ht := Module.finrank_mul_finrank K (R ⧸ AugmentedCotangent.ideal ε) (AugmentedCotangent.ideal ε).Cotangent
  rw [hf, one_mul] at ht
  rw [← ht, ideal_eq]
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance

theorem jet_dimension [IsRegularLocalRing R] (m : ℕ) (hd : ringKrullDim R = m) :
    Module.finrank K (K × (AugmentedCotangent.ideal ε).Cotangent) = m + 1 := by
  let := finite_cotangent ε
  have hm : Module.finrank K (AugmentedCotangent.ideal ε).Cotangent = m := by
    exact_mod_cast (cotangent_dimension ε).trans hd
  rw [Module.finrank_prod, Module.finrank_self, hm, add_comm]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedRegularJet
