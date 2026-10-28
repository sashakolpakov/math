import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ModuleDescent
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Module Unit Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ModuleUnitKernel

noncomputable section

/-! The kernel of the actual scalar-extension unit is the ideal times
the module. This supplies the algebra for successive nilpotent layers. -/

open _root_.CategoryTheory

universe u

theorem ideal_annihilates_module_quotient
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (I : Ideal R) :
    I ≤ Module.annihilator R (M ⧸ (I • (⊤ : Submodule R M))) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (r • m) = (0 : M ⧸ (I • (⊤ : Submodule R M)))
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr (Submodule.mem_top))

theorem quotientModule_unit_kernel
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app M).hom.ker =
      RingHom.ker f • (⊤ : Submodule R M) := by
  let I := RingHom.ker f
  let T := I • (⊤ : Submodule R M)
  let Q := ModuleCat.of R (M ⧸ T)
  let q : M ⟶ Q := ModuleCat.ofHom T.mkQ
  let adj := ModuleCat.extendRestrictScalarsAdj f
  have hQ : IsIso (adj.unit.app Q) :=
    ModuleDescent.quotientModule_unit_isIso f hf Q (ideal_annihilates_module_quotient M I)
  apply le_antisymm
  · intro m hm
    apply (Submodule.Quotient.mk_eq_zero T).mp
    apply (ConcreteCategory.bijective_of_isIso (adj.unit.app Q)).injective
    rw [map_zero]
    have hn := ConcreteCategory.congr_hom (adj.unit.naturality q) m
    simp only [Functor.id_map, ConcreteCategory.comp_apply] at hn
    have hz : adj.unit.app M m = 0 := hm
    rw [hz, map_zero] at hn
    exact hn
  · apply Submodule.smul_le.mpr
    intro r hr m _
    change adj.unit.app M (r • m) = 0
    rw [map_smul]
    change f r • (show (ModuleCat.extendScalars f).obj M from adj.unit.app M m) = 0
    rw [RingHom.mem_ker.mp hr, zero_smul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ModuleUnitKernel
