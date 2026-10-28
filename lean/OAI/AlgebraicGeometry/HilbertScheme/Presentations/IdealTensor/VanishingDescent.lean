import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExtendedIdealTensorCoefficients

/-! # Vanishing Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.VanishingDescent

noncomputable section

/-! Vanishing after extension of an ideal descends to a finite coefficient
algebra. The proof lifts through a free presentation of the module. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]
variable (C : Subalgebra B A) [Algebra.FiniteType B C]
variable {M : Type w} [AddCommGroup M] [Module B M]

theorem idealCoefficientTensor_zero_finite_descent (I : Ideal B) (x : M ⊗[B] I)
    (hx : (BaseChange.idealCoefficientInclusion B A I).lTensor M x = 0) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      (BaseChange.idealCoefficientInclusion B D I).lTensor M x = 0 := by
  classical
  let F := M →₀ B
  let q : F →ₗ[B] M := Finsupp.linearCombination B id
  have hq : Function.Surjective q := Finsupp.linearCombination_id_surjective B M
  obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective I hq x
  let IA := I.map (algebraMap B A)
  let αA := BaseChange.idealCoefficientInclusion B A I
  have hsquare : (q.rTensor IA).comp (αA.lTensor F) =
      (αA.lTensor M).comp (q.rTensor I) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hz : q.rTensor IA (αA.lTensor F y) = 0 := by
    have h := LinearMap.congr_fun hsquare y
    have hxA : αA.lTensor M x = 0 := hx
    simpa only [LinearMap.comp_apply, hy, hxA] using h
  have hex := rTensor_exact (M := q.ker) IA q.exact_subtype_ker_map hq
  obtain ⟨w, hw⟩ := (hex _).mp hz
  obtain ⟨D, hCD, hD, v, hv⟩ :=
    ExtendedIdealTensorCoefficients.extendedIdealTensor_finite_coefficient_representation C (M := q.ker) I w
  refine ⟨D, hCD, hD, ?_⟩
  let ID := I.map (algebraMap B D)
  let αD := BaseChange.idealCoefficientInclusion B D I
  let j := ExtendedIdealTensorCoefficients.extendedIdealInclusion D I
  have hksquare : (j.lTensor F).comp (q.ker.subtype.rTensor ID) =
      (q.ker.subtype.rTensor IA).comp (j.lTensor q.ker) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have he : q.ker.subtype.rTensor ID v = αD.lTensor F y := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := F) j
      (ExtendedIdealTensorCoefficients.extendedIdealInclusion_injective D I)
    calc
      j.lTensor F (q.ker.subtype.rTensor ID v) =
          q.ker.subtype.rTensor IA (j.lTensor q.ker v) := LinearMap.congr_fun hksquare v
      _ = q.ker.subtype.rTensor IA w := by rw [hv]
      _ = αA.lTensor F y := hw
      _ = j.lTensor F (αD.lTensor F y) := by
        rw [← LinearMap.lTensor_comp_apply]
        exact congrArg (fun f => f.lTensor F y) (ExtendedIdealTensorCoefficients.extendedIdealInclusion_coefficient D I).symm
  have hd := rTensor_exact (M := q.ker) ID q.exact_subtype_ker_map hq
  have hzero := hd.apply_apply_eq_zero v
  rw [he] at hzero
  have hsquareD : (q.rTensor ID).comp (αD.lTensor F) =
      (αD.lTensor M).comp (q.rTensor I) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have h := (LinearMap.congr_fun hsquareD y).symm.trans hzero
  simpa only [LinearMap.comp_apply, hy] using h

theorem idealTensorBaseChange_zero_finite_descent (I : Ideal B) (x : M ⊗[B] I)
    (hx : BaseChange.idealTensorBaseChangeMap B A M I x = 0) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      BaseChange.idealTensorBaseChangeMap B D M I x = 0 := by
  have hx' : (BaseChange.idealCoefficientInclusion B A I).lTensor M x = 0 := by
    have h := congrArg (BaseChange.idealTensorBaseChangeComparison B A M I) hx
    simpa only [BaseChange.idealTensorBaseChangeMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, map_zero] using h
  obtain ⟨D, hCD, hD, hz⟩ := idealCoefficientTensor_zero_finite_descent C I x hx'
  refine ⟨D, hCD, hD, ?_⟩
  simp only [BaseChange.idealTensorBaseChangeMap, LinearMap.comp_apply, hz, map_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.VanishingDescent
