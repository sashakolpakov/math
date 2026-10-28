import Mathlib.RingTheory.Smooth.Basic

/-! # Conormal Derivation Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalDerivationLift.Construction

noncomputable section

section

/-! Relative derivations on a quotient lift through a formally smooth ambient algebra. -/

theorem exists_quotient_derivation_lift
    (k : Type*) {R Q : Type*} [CommRing k] [CommRing R] [CommRing Q]
    [Algebra k R] [Algebra k Q] [Algebra.FormallySmooth k R]
    (φ : R →ₐ[k] Q) (hφ : Function.Surjective φ) (D : Derivation k Q Q) :
    ∃ E : Derivation k R R, ∀ r : R, φ (E r) = D (φ r) := by
  let : Algebra R Q := φ.toRingHom.toAlgebra
  let : IsScalarTower k R Q := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let d : Derivation k R Q := D.compAlgebraMap R
  let q : R →ₗ[R] Q := Algebra.linearMap R Q
  obtain ⟨e, he⟩ := Module.projective_lifting_property q d.liftKaehlerDifferential hφ
  refine ⟨e.compDer (KaehlerDifferential.D k R), ?_⟩
  intro r
  have h := LinearMap.congr_fun he (KaehlerDifferential.D k R r)
  change φ (e (KaehlerDifferential.D k R r)) = D (φ r)
  exact h.trans (d.liftKaehlerDifferential_comp_D r)

theorem exists_quotient_derivation_lift_annihilating_normal
    (k : Type*) {R Q : Type*} [CommRing k] [CommRing R] [CommRing Q]
    [Algebra k R] [Algebra k Q] [Algebra.FormallySmooth k R]
    (φ : R →ₐ[k] Q) (hφ : Function.Surjective φ) (D : Derivation k Q Q)
    (z : R) (hz : φ z = 0) (N : Derivation k R R) (hN : N z = 1) :
    ∃ E : Derivation k R R, E z = 0 ∧ ∀ r : R, φ (E r) = D (φ r) := by
  obtain ⟨E, hE⟩ := exists_quotient_derivation_lift k φ hφ D
  refine ⟨E - E z • N, ?_, ?_⟩
  · simp only [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hN, mul_one, sub_self]
  · intro r
    simp only [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, map_sub, map_mul,
      hE r, hE z, hz, map_zero, zero_mul, sub_zero]

end

section

/-! Prescribed conormal functionals of a smooth quotient are induced by actual ambient derivations. -/

open scoped TensorProduct

theorem exists_relative_derivation_lift_of_surjective
    (k : Type*) {R Q : Type*} [CommRing k] [CommRing R] [CommRing Q]
    [Algebra k R] [Algebra k Q] [Algebra R Q] [IsScalarTower k R Q]
    [Algebra.FormallySmooth k R] (hq : Function.Surjective (algebraMap R Q))
    (d : Derivation k R Q) :
    ∃ E : Derivation k R R, ∀ r, algebraMap R Q (E r) = d r := by
  obtain ⟨e, he⟩ := Module.projective_lifting_property (Algebra.linearMap R Q) d.liftKaehlerDifferential hq
  refine ⟨e.compDer (KaehlerDifferential.D k R), ?_⟩
  intro r
  have h := LinearMap.congr_fun he (KaehlerDifferential.D k R r)
  exact h.trans (d.liftKaehlerDifferential_comp_D r)

theorem exists_ambient_derivation_of_conormal_functional
    (k : Type*) {R Q : Type*} [CommRing k] [CommRing R] [CommRing Q]
    [Algebra k R] [Algebra k Q] [Algebra R Q] [IsScalarTower k R Q]
    [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k Q]
    (hq : Function.Surjective (algebraMap R Q))
    (L : (RingHom.ker (algebraMap R Q)).Cotangent →ₗ[R] Q) :
    ∃ E : Derivation k R R, ∀ x : RingHom.ker (algebraMap R Q),
      algebraMap R Q (E x.val) = L (Ideal.toCotangent _ x) := by
  obtain ⟨s, hs⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) hq).mp inferInstance
  let t : KaehlerDifferential k R →ₗ[R] Q :=
    L.comp (s.comp (TensorProduct.mk R Q (KaehlerDifferential k R) 1))
  let d : Derivation k R Q := t.compDer (KaehlerDifferential.D k R)
  obtain ⟨E, hE⟩ := exists_relative_derivation_lift_of_surjective k hq d
  refine ⟨E, ?_⟩
  intro x
  rw [hE]
  change L (s (1 ⊗ₜ[R] KaehlerDifferential.D k R x.val)) = L (Ideal.toCotangent _ x)
  apply congrArg L
  have h := LinearMap.congr_fun hs (Ideal.toCotangent _ x)
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    KaehlerDifferential.kerCotangentToTensor_toCotangent] using h

end

/-! A smooth quotient of a formally smooth algebra has a projective conormal module. -/

theorem smooth_extension_conormal_projective
    {k Q : Type*} [CommRing k] [CommRing Q] [Algebra k Q]
    (P : Algebra.Extension k Q) [Algebra.FormallySmooth k P.Ring] [Algebra.FormallySmooth k Q] :
    Module.Projective Q P.Cotangent := by
  obtain ⟨s, hs⟩ := P.formallySmooth_iff_split_injection.mp inferInstance
  exact Module.Projective.of_split P.cotangentComplex s hs

theorem smooth_extension_conormal_finite_projective
    {k Q : Type*} [CommRing k] [CommRing Q] [Algebra k Q]
    (P : Algebra.Extension k Q) [Algebra.FormallySmooth k P.Ring] [Algebra.FormallySmooth k Q]
    (hP : P.ker.FG) : Module.Finite Q P.Cotangent ∧ Module.Projective Q P.Cotangent :=
  ⟨Algebra.Extension.Cotangent.finite hP, smooth_extension_conormal_projective P⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalDerivationLift.Construction
