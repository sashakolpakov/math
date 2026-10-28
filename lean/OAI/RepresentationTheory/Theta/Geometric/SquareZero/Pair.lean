import OAI.RepresentationTheory.Theta.Geometric.Square.ZeroUnitNaturality

/-! # Pair -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.Pair

noncomputable section

section

/-! Coefficients compatible on the two copies of the quotient algebra
descend to constants plus the square-zero ideal. This form applies
directly to the compatibility of a normalized native isomorphism. -/

open scoped TensorProduct

variable {M R S B : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
    [IsCentralScalar ℂ M] [CommRing R] [Algebra ℂ R]
    [CommRing S] [Algebra ℂ S] [CommRing B] [Algebra ℂ B]

theorem squareZeroTensor_exists_lift_of_reduction_constant
    (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0) (q : R →ₐ[ℂ] S)
    (he : Function.Exact i q.toLinearMap) (x : R ⊗[ℂ] B) (b : B)
    (hx : Algebra.TensorProduct.map q (AlgHom.id ℂ B) x = Algebra.TensorProduct.includeRight b) :
    ∃ y : TrivSqZeroExt ℂ M ⊗[ℂ] B,
      Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B) y = x := by
  have hk : q.toLinearMap.rTensor B (x - Algebra.TensorProduct.includeRight b) = 0 := by
    change Algebra.TensorProduct.map q (AlgHom.id ℂ B) (x - Algebra.TensorProduct.includeRight b) = 0
    simp only [map_sub, hx, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, sub_self]
  obtain ⟨m, hm⟩ := (Module.Flat.rTensor_exact B he (x - Algebra.TensorProduct.includeRight b)).mp hk
  refine ⟨Algebra.TensorProduct.includeRight b + (TrivSqZeroExt.inrHom ℂ M).rTensor B m, ?_⟩
  rw [map_add, TensorDescent.squareZeroTensorMap_inr, hm]
  simp only [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
    map_one, AlgHom.id_apply, add_sub_cancel]

theorem squareZeroTensor_exists_lift_of_reduction_compatible [Nontrivial S]
    (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0) (q : R →ₐ[ℂ] S)
    (he : Function.Exact i q.toLinearMap) (x : R ⊗[ℂ] B)
    (hx : Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B) (Algebra.TensorProduct.map q (AlgHom.id ℂ B) x) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B) (Algebra.TensorProduct.map q (AlgHom.id ℂ B) x)) :
    ∃ y : TrivSqZeroExt ℂ M ⊗[ℂ] B,
      Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B) y = x := by
  obtain ⟨b, hb⟩ := Square.ZeroUnitNaturality.tensor_constant_of_two_copies_eq _ hx
  exact squareZeroTensor_exists_lift_of_reduction_constant i hsq q he x b hb.symm

theorem squareZeroTensor_exists_unit_lift_of_reduction_compatible [Nontrivial R] [Nontrivial S]
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap) (x : (R ⊗[ℂ] B)ˣ)
    (hx : Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B) (Algebra.TensorProduct.map q (AlgHom.id ℂ B) (x : R ⊗[ℂ] B)) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B) (Algebra.TensorProduct.map q (AlgHom.id ℂ B) (x : R ⊗[ℂ] B))) :
    ∃! y : (TrivSqZeroExt ℂ M ⊗[ℂ] B)ˣ,
      Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B)
        (y : TrivSqZeroExt ℂ M ⊗[ℂ] B) = x := by
  let f := (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S)
    (AlgHom.id ℂ B)).comp (Algebra.TensorProduct.map q (AlgHom.id ℂ B))
  let g := (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S)
    (AlgHom.id ℂ B)).comp (Algebra.TensorProduct.map q (AlgHom.id ℂ B))
  have hxu : Units.map f.toMonoidHom x = Units.map g.toMonoidHom x := Units.ext hx
  have hx' : f (↑x⁻¹ : R ⊗[ℂ] B) = g (↑x⁻¹ : R ⊗[ℂ] B) :=
    congrArg (fun u : ((S ⊗[ℂ] S) ⊗[ℂ] B)ˣ => (↑u⁻¹ : (S ⊗[ℂ] S) ⊗[ℂ] B)) hxu
  obtain ⟨y, hy⟩ := squareZeroTensor_exists_lift_of_reduction_compatible i hsq q he _ hx
  obtain ⟨z, hz⟩ := squareZeroTensor_exists_lift_of_reduction_compatible i hsq q he _ hx'
  have hinj := TensorDescent.squareZeroTensorMap_injective (B := B) i hi hsq
  have hyz : y * z = 1 := by
    apply hinj
    rw [map_mul, hy, hz, map_one]
    exact x.val_inv
  let u : (TrivSqZeroExt ℂ M ⊗[ℂ] B)ˣ := ⟨y, z, hyz, (mul_comm z y).trans hyz⟩
  refine ⟨u, hy, ?_⟩
  intro v hv
  exact Units.ext (hinj (hv.trans hy.symm))

end

section

/-! The two quotient-algebra maps have the same restriction to the
actual split square-zero subalgebra, including after tensoring. -/

open scoped TensorProduct

variable {M R S B : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
    [IsCentralScalar ℂ M] [CommRing R] [Algebra ℂ R]
    [CommRing S] [Algebra ℂ S] [CommRing B] [Algebra ℂ B]

theorem squareZero_quotient_two_maps_eq (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap) :
    ((Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S).comp q).comp
        (Subalgebra.squareZeroSubalgebraMap i hsq) =
      ((Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S).comp q).comp
        (Subalgebra.squareZeroSubalgebraMap i hsq) := by
  apply AlgHom.ext
  intro z
  have hz : q (i z.snd) = 0 := he.apply_apply_eq_zero z.snd
  simp only [AlgHom.comp_apply, Subalgebra.squareZeroSubalgebraMap_apply, map_add, hz,
    map_zero, add_zero, AlgHom.commutes]

theorem squareZeroTensor_quotient_two_maps_eq (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap) :
    ((Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B)).comp (Algebra.TensorProduct.map q (AlgHom.id ℂ B))).comp
        (Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B)) =
      ((Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B)).comp (Algebra.TensorProduct.map q (AlgHom.id ℂ B))).comp
        (Algebra.TensorProduct.map (Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B)) := by
  simp only [← Algebra.TensorProduct.map_comp, AlgHom.id_comp,
    squareZero_quotient_two_maps_eq i hsq q he]

end

section

/-! Constants plus the square-zero ideal are the exact equalizer of
the two maps through the quotient algebra. -/

open scoped TensorProduct

theorem scalar_of_tensor_inclusions_eq {S : Type*} [CommRing S] [Algebra ℂ S] [Nontrivial S]
    (s : S) (h : (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S) s =
      (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S) s) :
    ∃ c : ℂ, algebraMap ℂ S c = s := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ (show (1 : S) ≠ 0 from one_ne_zero)
  have H := congrArg ((TensorProduct.lid ℂ S).toLinearMap.comp (l.rTensor S)) h
  refine ⟨l s, ?_⟩
  simpa [hl, Algebra.smul_def] using H

variable {M R S : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
    [IsCentralScalar ℂ M] [CommRing R] [Algebra ℂ R]
    [CommRing S] [Algebra ℂ S] [Nontrivial S]

theorem squareZero_exists_lift_of_quotient_pair_eq
    (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0) (q : R →ₐ[ℂ] S)
    (he : Function.Exact i q.toLinearMap) (r : R)
    (hr : (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S) (q r) =
      (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S) (q r)) :
    ∃ a : TrivSqZeroExt ℂ M, Subalgebra.squareZeroSubalgebraMap i hsq a = r := by
  obtain ⟨c, hc⟩ := scalar_of_tensor_inclusions_eq (q r) hr
  have hq : q.toLinearMap (r - algebraMap ℂ R c) = 0 := by
    change q (r - algebraMap ℂ R c) = 0
    rw [map_sub, q.commutes, hc, sub_self]
  obtain ⟨m, hm⟩ := (he _).mp hq
  refine ⟨TrivSqZeroExt.inl c + TrivSqZeroExt.inr m, ?_⟩
  change algebraMap ℂ R (c + 0) + i (0 + m) = r
  rw [add_zero, zero_add, hm, add_sub_cancel]

end

/-! The quotient pair is an exact sequence of modules over the actual
square-zero subalgebra, so it can be used under flat chart extension. -/

open scoped TensorProduct

variable {M R S : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
    [IsCentralScalar ℂ M] [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    [Algebra (TrivSqZeroExt ℂ M) R] [Algebra (TrivSqZeroExt ℂ M) (S ⊗[ℂ] S)]
    (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0) (q : R →ₐ[ℂ] S)
    (he : Function.Exact i q.toLinearMap)
    (hk : ∀ a, algebraMap (TrivSqZeroExt ℂ M) R a = Subalgebra.squareZeroSubalgebraMap i hsq a)
    (hp : ∀ a, algebraMap (TrivSqZeroExt ℂ M) (S ⊗[ℂ] S) a =
      (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S) (q (Subalgebra.squareZeroSubalgebraMap i hsq a)))

def squareZeroFirstQuotientHom : R →ₐ[TrivSqZeroExt ℂ M] S ⊗[ℂ] S where
  __ := ((Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S).comp q).toRingHom
  commutes' a := by
    change (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S)
      (q (algebraMap (TrivSqZeroExt ℂ M) R a)) = _
    rw [hk, hp]

def squareZeroSecondQuotientHom : R →ₐ[TrivSqZeroExt ℂ M] S ⊗[ℂ] S where
  __ := ((Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S).comp q).toRingHom
  commutes' a := by
    change (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S)
      (q (algebraMap (TrivSqZeroExt ℂ M) R a)) = _
    rw [hk, hp]
    exact (DFunLike.congr_fun (squareZero_quotient_two_maps_eq i hsq q he) a).symm

theorem squareZero_quotient_pair_exact [Nontrivial S] :
    Function.Exact (Algebra.linearMap (TrivSqZeroExt ℂ M) R)
      ((squareZeroFirstQuotientHom i hsq q hk hp).toLinearMap -
        (squareZeroSecondQuotientHom i hsq q he hk hp).toLinearMap) := by
  intro r
  constructor
  · intro hr
    have hr' : (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S) (q r) =
        (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S) (q r) := sub_eq_zero.mp hr
    obtain ⟨a, ha⟩ := squareZero_exists_lift_of_quotient_pair_eq i hsq q he r hr'
    refine ⟨a, ?_⟩
    change algebraMap (TrivSqZeroExt ℂ M) R a = r
    rw [hk, ha]
  · rintro ⟨a, rfl⟩
    change squareZeroFirstQuotientHom i hsq q hk hp (algebraMap (TrivSqZeroExt ℂ M) R a) -
      squareZeroSecondQuotientHom i hsq q he hk hp (algebraMap (TrivSqZeroExt ℂ M) R a) = 0
    rw [AlgHom.commutes, AlgHom.commutes, sub_self]

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.Pair
