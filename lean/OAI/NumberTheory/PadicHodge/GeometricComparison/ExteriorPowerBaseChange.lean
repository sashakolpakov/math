import OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorAlgebraBaseChange
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Flat.Basic

/-! # Exterior Power Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerBaseChange.ExteriorBaseChange

noncomputable section

section

/-! Flat scalar extension embeds every exterior power into the exterior power of the extended module. -/

open scoped TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [AddCommGroup M]
  [Algebra R S] [Module R M] [Invertible (2 : R)]

def algebraMap : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S (S ⊗[R] M) :=
  ((ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv R S M).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

theorem algebraMap_ι (m : M) :
    algebraMap R S M (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι S (1 ⊗ₜ[R] m) :=
  ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv_tmul_ι R S M 1 m

theorem algebraMap_ιMulti (n : ℕ) (v : Fin n → M) :
    algebraMap R S M (ExteriorAlgebra.ιMulti R n v) =
      ExteriorAlgebra.ιMulti S n (fun i => 1 ⊗ₜ[R] v i) := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, Function.comp_def,
    algebraMap_ι]

theorem algebraEquiv_tmul_ιMulti (n : ℕ) (s : S) (v : Fin n → M) :
    ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv R S M (s ⊗ₜ[R] ExteriorAlgebra.ιMulti R n v) =
      s • ExteriorAlgebra.ιMulti S n (fun i => 1 ⊗ₜ[R] v i) := by
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
  exact congrArg (s • ·) (algebraMap_ιMulti R S M n v)

theorem algebraEquiv_tmul_power_mem (n : ℕ) (s : S) (ω : ⋀[R]^n M) :
    ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv R S M (s ⊗ₜ[R] (ω : ExteriorAlgebra R M)) ∈ ⋀[S]^n (S ⊗[R] M) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    change ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv R S M (s ⊗ₜ[R] ExteriorAlgebra.ιMulti R n v) ∈ _
    rw [algebraEquiv_tmul_ιMulti]
    exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range S n (Set.mem_range_self _))
  | zero => simp only [ZeroMemClass.coe_zero, TensorProduct.tmul_zero, map_zero, zero_mem]
  | add x y hx hy ihx ihy =>
    simpa only [Submodule.coe_add, TensorProduct.tmul_add, map_add] using
      Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    change ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv R S M (s ⊗ₜ[R] (r • (x : ExteriorAlgebra R M))) ∈ _
    rw [TensorProduct.tmul_smul]
    change ((ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv R S M).toLinearEquiv.restrictScalars R)
      (r • (s ⊗ₜ[R] (x : ExteriorAlgebra R M))) ∈ _
    rw [map_smul]
    exact ((⋀[S]^n (S ⊗[R] M)).restrictScalars R).smul_mem r ih

def powerAmbientMap (n : ℕ) : S ⊗[R] (⋀[R]^n M) →ₗ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  (ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv R S M).toLinearMap.comp ((⋀[R]^n M).subtype.baseChange S)

theorem powerAmbientMap_mem (n : ℕ) (x : S ⊗[R] (⋀[R]^n M)) :
    powerAmbientMap R S M n x ∈ ⋀[S]^n (S ⊗[R] M) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul s ω => exact algebraEquiv_tmul_power_mem R S M n s ω

def powerScalarMap (n : ℕ) : S ⊗[R] (⋀[R]^n M) →ₗ[S] ⋀[S]^n (S ⊗[R] M) :=
  (powerAmbientMap R S M n).codRestrict _ (powerAmbientMap_mem R S M n)

theorem powerScalarMap_injective [Module.Flat R S] (n : ℕ) :
    Function.Injective (powerScalarMap R S M n) := by
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (M := S) (⋀[R]^n M).subtype Subtype.val_injective
  apply (ExteriorAlgebraBaseChange.ExteriorBaseChange.algebraEquiv R S M).injective
  exact congrArg Subtype.val h

end

/-! Every exterior power commutes with flat scalar extension when two is invertible. -/

open scoped TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [AddCommGroup M]
  [Algebra R S] [Module R M] [Invertible (2 : R)]

omit [Invertible (2 : R)] in
theorem one_tmul_span :
    Submodule.span S (Set.range (fun m : M => (1 : S) ⊗ₜ[R] m)) = ⊤ := by
  apply top_unique
  intro x _
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul s m =>
    rw [TensorProduct.tmul_eq_smul_one_tmul]
    exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_range_self m))

theorem powerScalarMap_tmul_ιMulti (n : ℕ) (s : S) (v : Fin n → M) :
    powerScalarMap R S M n (s ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      s • exteriorPower.ιMulti S n (fun i => 1 ⊗ₜ[R] v i) := by
  apply Subtype.ext
  exact algebraEquiv_tmul_ιMulti R S M n s v

theorem powerScalarMap_surjective (n : ℕ) : Function.Surjective (powerScalarMap R S M n) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← exteriorPower.ιMulti_span_of_span S n (S ⊗[R] M) (one_tmul_span R S M)]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  choose m hm using (fun i => hv (Set.mem_range_self i))
  refine ⟨1 ⊗ₜ[R] exteriorPower.ιMulti R n m, ?_⟩
  rw [powerScalarMap_tmul_ιMulti, one_smul]
  exact congrArg (exteriorPower.ιMulti S n) (funext hm)

def powerEquiv [Module.Flat R S] (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) ≃ₗ[S] ⋀[S]^n (S ⊗[R] M) :=
  LinearEquiv.ofBijective (powerScalarMap R S M n)
    ⟨powerScalarMap_injective R S M n, powerScalarMap_surjective R S M n⟩

theorem powerEquiv_tmul_ιMulti [Module.Flat R S] (n : ℕ) (s : S) (v : Fin n → M) :
    powerEquiv R S M n (s ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      s • exteriorPower.ιMulti S n (fun i => 1 ⊗ₜ[R] v i) :=
  powerScalarMap_tmul_ιMulti R S M n s v

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerBaseChange.ExteriorBaseChange
