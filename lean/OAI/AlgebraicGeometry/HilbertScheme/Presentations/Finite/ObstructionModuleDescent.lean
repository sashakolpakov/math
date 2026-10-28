import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.IdealTensorVanishing

/-! # Obstruction Module Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ObstructionModuleDescent

noncomputable section

/-! The whole finite obstruction module for one finitely generated ideal
vanishes over a finite coefficient algebra when the limit module is flat. -/

open TensorProduct

universe u v w t
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]
variable (S : Type w) [CommRing S] [Algebra B S] [IsNoetherianRing S]
variable (M : Type t) [AddCommGroup M] [Module B M] [Module S M] [IsScalarTower B S M]
variable [Module.Finite S M] [Module.Flat A (A ⊗[B] M)]

theorem idealTensorObstruction_finite_coefficient_descent
    (C : Subalgebra B A) [Algebra.FiniteType B C] (I : Ideal B) (hI : I.FG) :
    ∃ D : Subalgebra B A, C ≤ D ∧ Algebra.FiniteType B D ∧
      ∀ x : (IdealTensor.Obstruction.idealTensorMultiplication B S M I).ker,
        IdealTensor.BaseChange.idealTensorBaseChangeMap B D M I x.val = 0 := by
  classical
  let K := (IdealTensor.Obstruction.idealTensorMultiplication B S M I).ker
  let : Module.Finite S K := IdealTensor.Obstruction.idealTensorObstruction_finite B S M I hI
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule S K).FG)
  have hzero (r : s) : IdealTensor.BaseChange.idealTensorBaseChangeMap B A M I r.val.val = 0 :=
    IdealTensor.BaseChange.idealTensorObstruction_baseChange_zero B A M I ⟨r.val.val, r.val.property⟩
  obtain ⟨D, hCD, hD, hz⟩ := IdealTensorVanishing.finite_idealTensorBaseChange_zero_descent C I (fun r : s => r.val.val) hzero
  let α := IdealTensor.BaseChange.idealCoefficientInclusion B D I
  let g : K →ₗ[S] M ⊗[B] I.map (algebraMap B D) :=
    (AlgebraTensorModule.map (LinearMap.id : M →ₗ[S] M) α).comp K.subtype
  have hg (r : s) : g r.val = 0 := by
    have h := congrArg (IdealTensor.BaseChange.idealTensorBaseChangeComparison B D M I) (hz r)
    simpa only [IdealTensor.BaseChange.idealTensorBaseChangeMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, map_zero] using! h
  have hker : (⊤ : Submodule S K) ≤ g.ker := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    exact hg ⟨x, hx⟩
  refine ⟨D, hCD, hD, fun x => ?_⟩
  have hx : (IdealTensor.BaseChange.idealCoefficientInclusion B D I).lTensor M x.val = 0 :=
    hker (Submodule.mem_top : x ∈ (⊤ : Submodule S K))
  simp only [IdealTensor.BaseChange.idealTensorBaseChangeMap, LinearMap.comp_apply, hx, map_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ObstructionModuleDescent
