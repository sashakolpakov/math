import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality

/-! # Ideal Quotient Cochain Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IdealQuotientCochainProduct.Module

noncomputable section

/-! The native product and differential pass to the actual coefficient
quotient of a complex. The projection preserves products on cohomology. -/

open _root_.CategoryTheory

open _root_.Module

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R)
  (K : CochainComplex (ModuleCat.{v} R) ℕ)
  (μ : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m))

def complexPairing (n m : ℕ) : (Module.IdealQuotient.complex R I K).X n →ₗ[R]
    (Module.IdealQuotient.complex R I K).X m →ₗ[R] (Module.IdealQuotient.complex R I K).X (n + m) := Module.IdealQuotientProduct.pairing I (μ n m)

theorem projection_complexPairing (n m : ℕ) (x : K.X n) (y : K.X m) :
    complexPairing I K μ n m ((I • ⊤ : Submodule R (K.X n)).mkQ x)
        ((I • ⊤ : Submodule R (K.X m)).mkQ y) =
      (I • ⊤ : Submodule R (K.X (n + m))).mkQ (μ n m x y) := rfl

theorem quotient_d_apply (n m : ℕ) (x : K.X n) :
    (Module.IdealQuotient.complex R I K).d n m ((I • ⊤ : Submodule R (K.X n)).mkQ x) =
      (I • ⊤ : Submodule R (K.X m)).mkQ (K.d n m x) := rfl

theorem projection_cupInto (n m k : ℕ) (h : n + m = k) (x : K.X n) (y : K.X m) :
    (I • ⊤ : Submodule R (K.X k)).mkQ (Cochain.CohomologyCup.cupInto K μ n m k h x y) =
      Cochain.CohomologyCup.cupInto (Module.IdealQuotient.complex R I K) (complexPairing I K μ) n m k h
        ((I • ⊤ : Submodule R (K.X n)).mkQ x) ((I • ⊤ : Submodule R (K.X m)).mkQ y) := by
  subst k
  rfl

variable (hμ : ∀ n m (x : K.X n) (y : K.X m),
  K.d (n + m) (n + m + 1) (μ n m x y) =
    Cochain.CohomologyCup.cupInto K μ (n + 1) m (n + m + 1) (by omega) (K.d n (n + 1) x) y +
    (-1 : ℤ) ^ n • Cochain.CohomologyCup.cupInto K μ n (m + 1) (n + m + 1) (by omega)
      x (K.d m (m + 1) y))

include hμ in
theorem differential_complexPairing (n m : ℕ)
    (x : (Module.IdealQuotient.complex R I K).X n) (y : (Module.IdealQuotient.complex R I K).X m) :
    (Module.IdealQuotient.complex R I K).d (n + m) (n + m + 1) (complexPairing I K μ n m x y) =
      Cochain.CohomologyCup.cupInto (Module.IdealQuotient.complex R I K) (complexPairing I K μ)
        (n + 1) m (n + m + 1) (by omega) ((Module.IdealQuotient.complex R I K).d n (n + 1) x) y +
      (-1 : ℤ) ^ n • Cochain.CohomologyCup.cupInto (Module.IdealQuotient.complex R I K) (complexPairing I K μ)
        n (m + 1) (n + m + 1) (by omega) x ((Module.IdealQuotient.complex R I K).d m (m + 1) y) := by
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R (K.X n)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R (K.X m)).mkQ_surjective y
  rw [projection_complexPairing, quotient_d_apply, hμ, map_add, map_zsmul,
    projection_cupInto, projection_cupInto, quotient_d_apply, quotient_d_apply]
  rfl

def quotientCohomologyCup (n m : ℕ) : (Module.IdealQuotient.complex R I K).homology n →ₗ[R]
    (Module.IdealQuotient.complex R I K).homology m →ₗ[R] (Module.IdealQuotient.complex R I K).homology (n + m) :=
  Cochain.CohomologyCup.cohomologyCup (Module.IdealQuotient.complex R I K) (complexPairing I K μ)
    (differential_complexPairing I K μ hμ) n m

theorem projection_cohomologyCup (n m : ℕ) (x : K.homology n) (y : K.homology m) :
    HomologicalComplex.homologyMap (Module.IdealQuotient.complexProjection R I K) (n + m)
        (Cochain.CohomologyCup.cohomologyCup K μ hμ n m x y) =
      quotientCohomologyCup I K μ hμ n m
        (HomologicalComplex.homologyMap (Module.IdealQuotient.complexProjection R I K) n x)
        (HomologicalComplex.homologyMap (Module.IdealQuotient.complexProjection R I K) m y) :=
  Cochain.CupNaturality.Cohomology.cohomologyMap_cup μ (complexPairing I K μ) hμ
    (differential_complexPairing I K μ hμ) (Module.IdealQuotient.complexProjection R I K)
    (fun n m x y => (projection_complexPairing I K μ n m x y).symm) n m x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IdealQuotientCochainProduct.Module
