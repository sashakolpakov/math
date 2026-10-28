import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExactKernelPair
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasicoherentKernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.Additivity

/-! # Exact Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ExactEuler

noncomputable section

/-! Euler additivity telescopes along the kernels of a bounded exact coherent complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem coefficientEulerCharacteristic_of_isZero
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (M : X.Modules) (hM : IsZero M) : CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M = 0 := by
  unfold CohomologyEulerCharacteristic.coefficientEulerCharacteristic
  calc
    _ = ∑ᶠ _q : ℕ, (0 : ℤ) := by
      apply finsum_congr
      intro q
      have hz := Functor.map_isZero
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q) hM
      have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
          (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) := ModuleCat.isZero_iff_subsingleton.mp hz
      simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]
    _ = 0 := finsum_zero

theorem kernel_isZero_of_source_isZero {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (hM : IsZero M) : IsZero (kernel f) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (kernel.ι f)).mp
  simp only [Category.id_comp, zero_comp]
  exact hM.eq_of_tgt _ _

theorem exact_kernel_isZero_of_first_isZero {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.Exact) (hX : IsZero S.X₁) :
    IsZero (kernel S.g) := by
  let q := kernel.lift S.g S.f S.zero
  have : Epi q := hS.epi_kernelLift
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi q).mp
  simp only [Category.comp_id, comp_zero]
  exact hX.eq_of_src _ _

theorem proper_coherent_exact_kernel_euler
    {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ Spec (.of k)) [IsProper p] (S : ShortComplex X.Modules) (hS : S.Exact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    [S.X₁.IsFiniteType] [S.X₂.IsFiniteType] :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p S.X₁ =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel S.f) +
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (kernel S.g) := by
  have := Quasicoherent.Kernels.module_quasicoherent_kernel S.f
  have := Quasicoherent.Kernels.module_quasicoherent_kernel S.g
  have := Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType S.f
  have := Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType S.g
  exact @Proper.CohomologyEulerAdditivity.proper_coherent_euler_additive k _ X p _ (ExactKernelPair.exactKernelPair S)
    (ExactKernelPair.exactKernelPair_shortExact S hS)
    (Quasicoherent.Kernels.module_quasicoherent_kernel S.f) (Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType S.f)
    (inferInstance : S.X₁.IsQuasicoherent) (inferInstance : S.X₁.IsFiniteType)
    (Quasicoherent.Kernels.module_quasicoherent_kernel S.g) (Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType S.g)

theorem alternating_sum_of_adjacent_balance (a b : ℕ → ℤ)
    (hzero : a 0 = b 0) (hstep : ∀ n, a (n + 1) = b (n + 1) + b n) (r : ℕ) :
    (∑ n ∈ Finset.range (r + 1), (-1 : ℤ) ^ n * a n) = (-1 : ℤ) ^ r * b r := by
  induction r with
  | zero => simpa using hzero
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, hstep r, pow_succ]
    ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ExactEuler
