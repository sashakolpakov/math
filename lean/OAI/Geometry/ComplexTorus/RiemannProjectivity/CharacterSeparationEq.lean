import OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineCone

/-! # Character Separation Eq -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.CharacterSeparationEq.Constructions.CharacterSeparation

noncomputable section

/-! # RiemannProjectivity: complex algebra points detect elements of a reduced finite-type algebra -/

variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

theorem isNilpotent_of_all_points_zero (a : A) (ha : ∀ q : A →ₐ[ℂ] ℂ, q a = 0) :
    IsNilpotent a := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType ℂ A)
  obtain ⟨p, rfl⟩ := hf a
  have hp : p ∈ MvPolynomial.vanishingIdeal ℂ
      (MvPolynomial.zeroLocus ℂ (RingHom.ker f.toRingHom)) := by
    intro x hx
    let q : A →ₐ[ℂ] ℂ := AlgHom.liftOfSurjective f hf (MvPolynomial.aeval x) hx
    exact (AlgHom.liftOfSurjective_apply f hf (MvPolynomial.aeval x) hx p).symm.trans (ha q)
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hp
  obtain ⟨k, hk⟩ := hp
  refine ⟨k, ?_⟩
  change f (p ^ k) = 0 at hk
  rwa [map_pow] at hk

theorem eq_zero_of_all_points_zero [IsReduced A]
    (a : A) (ha : ∀ q : A →ₐ[ℂ] ℂ, q a = 0) : a = 0 :=
  IsReduced.eq_zero a (isNilpotent_of_all_points_zero a ha)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.CharacterSeparationEq.Constructions.CharacterSeparation
