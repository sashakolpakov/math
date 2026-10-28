import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Differential Base Iso -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialBaseIso

noncomputable section

/-!
# Kähler differentials under an isomorphism of the base ring

Changing the base ring along a surjective map does not change the module of
differentials of an algebra over the target. In particular, this gives explicit
transport along a base-ring isomorphism, with the induced scalar structure.
-/

section SurjectiveBase

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The universal `R`-derivation is also `S`-linear when `R → S` is surjective. -/
def kaehlerDerivationOfSurjectiveBase
    (h : Function.Surjective (algebraMap R S)) : Derivation S T Ω[T⁄R] where
  toFun := KaehlerDifferential.D R T
  map_add' := map_add (KaehlerDifferential.D R T)
  map_smul' s x := by
    obtain ⟨r, rfl⟩ := h s
    simpa only [RingHom.id_apply, IsScalarTower.algebraMap_smul] using
      (KaehlerDifferential.D R T).map_smul r x
  map_one_eq_zero' := (KaehlerDifferential.D R T).map_one_eq_zero
  leibniz' := (KaehlerDifferential.D R T).leibniz

@[simp]
theorem kaehlerDerivationOfSurjectiveBase_apply
    (h : Function.Surjective (algebraMap R S)) (x : T) :
    kaehlerDerivationOfSurjectiveBase R S T h x = KaehlerDifferential.D R T x := rfl

/-- A surjective change of base gives an actual linear equivalence between
the two modules of Kähler differentials. -/
def kaehlerDifferentialEquivOfSurjectiveBase
    (h : Function.Surjective (algebraMap R S)) : Ω[T⁄R] ≃ₗ[T] Ω[T⁄S] := by
  let f := KaehlerDifferential.map R S T T
  let g := (kaehlerDerivationOfSurjectiveBase R S T h).liftKaehlerDifferential
  have hgf : g.comp f = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [f, g]
  have hfg : f.comp g = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [f, g]
  exact
    { f with
      invFun := g
      left_inv := fun x => LinearMap.congr_fun hgf x
      right_inv := fun x => LinearMap.congr_fun hfg x }

@[simp]
theorem kaehlerDifferentialEquivOfSurjectiveBase_D
    (h : Function.Surjective (algebraMap R S)) (x : T) :
    kaehlerDifferentialEquivOfSurjectiveBase R S T h (KaehlerDifferential.D R T x) =
      KaehlerDifferential.D S T x := by
  change KaehlerDifferential.map R S T T (KaehlerDifferential.D R T x) = _
  simp

@[simp]
theorem kaehlerDifferentialEquivOfSurjectiveBase_symm_D
    (h : Function.Surjective (algebraMap R S)) (x : T) :
    (kaehlerDifferentialEquivOfSurjectiveBase R S T h).symm
        (KaehlerDifferential.D S T x) = KaehlerDifferential.D R T x := by
  apply (kaehlerDifferentialEquivOfSurjectiveBase R S T h).injective
  simp

theorem kaehlerDifferential_rank_eq_of_surjectiveBase
    (h : Function.Surjective (algebraMap R S)) :
    Module.rank T Ω[T⁄R] = Module.rank T Ω[T⁄S] :=
  (kaehlerDifferentialEquivOfSurjectiveBase R S T h).rank_eq

theorem kaehlerDifferential_finrank_eq_of_surjectiveBase
    (h : Function.Surjective (algebraMap R S)) :
    Module.finrank T Ω[T⁄R] = Module.finrank T Ω[T⁄S] :=
  (kaehlerDifferentialEquivOfSurjectiveBase R S T h).finrank_eq

end SurjectiveBase

variable {R S : Type*} (T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R T]

/-- The scalar structure obtained by transporting the base along a ring
isomorphism. -/
abbrev differentialBaseIsoAlgebra (e : S ≃+* R) : Algebra S T :=
  ((algebraMap R T).comp e.toRingHom).toAlgebra

/-- Kähler differentials are unchanged by transporting the base ring through
an isomorphism. The new scalar structure is specified by composition. -/
def kaehlerDifferentialBaseIso (e : S ≃+* R) :
    letI := differentialBaseIsoAlgebra T e
    Ω[T⁄R] ≃ₗ[T] Ω[T⁄S] := by
  let := differentialBaseIsoAlgebra T e
  let : Algebra S R := e.toRingHom.toAlgebra
  have : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (kaehlerDifferentialEquivOfSurjectiveBase S R T e.surjective).symm

@[simp]
theorem kaehlerDifferentialBaseIso_D (e : S ≃+* R) (x : T) :
    letI := differentialBaseIsoAlgebra T e
    kaehlerDifferentialBaseIso T e (KaehlerDifferential.D R T x) =
      KaehlerDifferential.D S T x := by
  let := differentialBaseIsoAlgebra T e
  let : Algebra S R := e.toRingHom.toAlgebra
  have : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact kaehlerDifferentialEquivOfSurjectiveBase_symm_D S R T e.surjective x

theorem kaehlerDifferential_rank_eq_of_baseIso (e : S ≃+* R) :
    letI := differentialBaseIsoAlgebra T e
    Module.rank T Ω[T⁄R] = Module.rank T Ω[T⁄S] := by
  let := differentialBaseIsoAlgebra T e
  exact (kaehlerDifferentialBaseIso T e).rank_eq

theorem kaehlerDifferential_finrank_eq_of_baseIso (e : S ≃+* R) :
    letI := differentialBaseIsoAlgebra T e
    Module.finrank T Ω[T⁄R] = Module.finrank T Ω[T⁄S] := by
  let := differentialBaseIsoAlgebra T e
  exact (kaehlerDifferentialBaseIso T e).finrank_eq

end

end OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialBaseIso
