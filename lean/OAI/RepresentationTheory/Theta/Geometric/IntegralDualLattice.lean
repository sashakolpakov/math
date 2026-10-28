import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Algebra.Module.ZLattice.Basic

/-! # Integral Dual Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntegralDualLattice

noncomputable section

/-! A nondegenerate real pairing identifies its integral dual lattice
with the full integer dual of the original lattice. -/

open _root_.Module

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (b : Basis I ℤ L) (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)

def latticeDualRealExtension (f : L →ₗ[ℤ] ℤ) : V →ₗ[ℝ] ℝ :=
  (b.ofZLatticeBasis ℝ L).constr ℝ (fun i => (f (b i) : ℝ))

omit [Fintype I] in
theorem latticeDualRealExtension_apply (f : L →ₗ[ℤ] ℤ) (v : L) :
    latticeDualRealExtension L b f v.val = (f v : ℝ) := by
  have h : ((latticeDualRealExtension L b f).restrictScalars ℤ).comp L.subtype =
      (Algebra.linearMap ℤ ℝ).comp f := by
    apply b.ext
    intro i
    change latticeDualRealExtension L b f (b i).val = (f (b i) : ℝ)
    rw [← b.ofZLatticeBasis_apply ℝ L i]
    exact (b.ofZLatticeBasis ℝ L).constr_basis ℝ _ i
  exact congrArg (fun q : L →ₗ[ℤ] ℝ => q v) h

include b hB in
omit [Fintype I] in
theorem dualSubmoduleToDual_surjective : Function.Surjective (B.dualSubmoduleToDual L) := by
  intro f
  let v := (B.toDual hB).symm (latticeDualRealExtension L b f)
  have hv (w : L) : B v w.val = (f w : ℝ) :=
    (B.apply_toDual_symm_apply (f := latticeDualRealExtension L b f) (v := w.val)).trans
      (latticeDualRealExtension_apply L b f w)
  have hvL : v ∈ B.dualSubmodule L := by
    intro w hw
    exact Submodule.mem_one.mpr ⟨f ⟨w, hw⟩, (hv ⟨w, hw⟩).symm⟩
  refine ⟨⟨v, hvL⟩, ?_⟩
  apply LinearMap.ext
  intro w
  apply Int.cast_injective (α := ℝ)
  exact (B.dualSubmoduleParing_spec ⟨v, hvL⟩ w).trans (hv w)

def integralDualLatticeEquiv : B.dualSubmodule L ≃ₗ[ℤ] (L →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective (B.dualSubmoduleToDual L)
    ⟨B.dualSubmoduleToDual_injective hB L (IsZLattice.span_top (K := ℝ) (L := L)),
      dualSubmoduleToDual_surjective L b B hB⟩

include b hB in
theorem dualLattice_discrete : DiscreteTopology (B.dualSubmodule L) := by
  classical
  rw [← b.ofZLatticeBasis_span ℝ L, B.dualSubmodule_span_of_basis hB (b.ofZLatticeBasis ℝ L)]
  infer_instance

theorem dualLattice_full :
    letI := dualLattice_discrete L b B hB
    IsZLattice ℝ (B.dualSubmodule L) := by
  let := dualLattice_discrete L b B hB
  classical
  constructor
  rw [← b.ofZLatticeBasis_span ℝ L, B.dualSubmodule_span_of_basis hB (b.ofZLatticeBasis ℝ L)]
  exact ZSpan.span_top (B.dualBasis hB (b.ofZLatticeBasis ℝ L))

end

end OAI.RepresentationTheory.Theta.Geometric.IntegralDualLattice
