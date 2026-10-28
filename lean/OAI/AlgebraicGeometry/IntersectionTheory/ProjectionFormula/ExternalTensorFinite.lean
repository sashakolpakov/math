import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensor
import Mathlib.RingTheory.Finiteness.Basic

/-! # External Tensor Finite -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorFinite

noncomputable section

/-! Finite generating sets of the two input modules give a finite
generating set of their external tensor product over the product ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

variable (K R S : Type u) [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
  (M N : Type u) [AddCommGroup M] [AddCommGroup N]
  [Module K M] [Module R M] [IsScalarTower K R M]
  [Module K N] [Module S N] [IsScalarTower K S N]

attribute [local instance] ExternalTensor.module

theorem finite [Module.Finite R M] [Module.Finite S N] :
    Module.Finite (R ⊗[K] S) (ExternalTensor.obj K R S M N) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R M).FG)
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule S N).FG)
  let U : Finset (ExternalTensor.obj K R S M N) :=
    (s ×ˢ t).image fun z => z.1 ⊗ₜ[K] z.2
  let V := Submodule.span (R ⊗[K] S) (U : Set (ExternalTensor.obj K R S M N))
  have hmem : ∀ m ∈ Submodule.span R (s : Set M), ∀ n ∈ Submodule.span S (t : Set N),
      m ⊗ₜ[K] n ∈ V := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      intro n hn
      induction hn using Submodule.span_induction with
      | mem n hn =>
        exact Submodule.subset_span (Finset.mem_image.mpr ⟨(m, n), Finset.mem_product.mpr ⟨hm, hn⟩, rfl⟩)
      | zero => simpa only [TensorProduct.tmul_zero] using V.zero_mem
      | add n n' _ _ hn hn' => simpa only [TensorProduct.tmul_add] using V.add_mem hn hn'
      | smul a n _ hn =>
        have hv := V.smul_mem ((1 : R) ⊗ₜ[K] a) hn
        change ((1 : R) • m) ⊗ₜ[K] (a • n) ∈ V at hv
        simpa only [one_smul] using hv
    | zero => intro n _; simpa only [TensorProduct.zero_tmul] using V.zero_mem
    | add m m' _ _ hm hm' =>
      intro n hn
      simpa only [TensorProduct.add_tmul] using V.add_mem (hm n hn) (hm' n hn)
    | smul a m _ hm =>
      intro n hn
      have hv := V.smul_mem (a ⊗ₜ[K] (1 : S)) (hm n hn)
      change (a • m) ⊗ₜ[K] ((1 : S) • n) ∈ V at hv
      simpa only [one_smul] using hv
  apply Module.Finite.of_fg_top
  refine ⟨U, eq_top_iff.mpr ?_⟩
  intro x _
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact hmem m (hs ▸ Submodule.mem_top) n (ht ▸ Submodule.mem_top)
  | add x y hx hy => exact V.add_mem (hx Submodule.mem_top) (hy Submodule.mem_top)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorFinite
