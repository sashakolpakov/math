import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Support
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Support

noncomputable section

/-! The support of the tensor product of two finite modules is
exactly the intersection of their supports. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

theorem field_nontrivial (k : Type u) [Field k] (M N : ModuleCat.{u} k) :
    Nontrivial (M ⊗[k] N) ↔ Nontrivial M ∧ Nontrivial N := by
  constructor
  · intro h
    let : Nontrivial (M ⊗[k] N) := h
    constructor
    · by_contra hm
      let : Subsingleton M := not_nontrivial_iff_subsingleton.mp hm
      exact not_subsingleton (M ⊗[k] N) inferInstance
    · by_contra hn
      let : Subsingleton N := not_nontrivial_iff_subsingleton.mp hn
      exact not_subsingleton (M ⊗[k] N) inferInstance
  · rintro ⟨hM, hN⟩
    let : Nontrivial M := hM
    let : Nontrivial N := hN
    infer_instance

theorem support (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] :
    Module.support R (M ⊗[R] N) = Module.support R M ∩ Module.support R N := by
  ext p
  rw [Set.mem_inter_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    (TensorProduct.AlgebraTensorModule.distribBaseChange R p.asIdeal.ResidueField M N).nontrivial_congr]
  exact field_nontrivial p.asIdeal.ResidueField
    (.of p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M))
    (.of p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] N))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Support
