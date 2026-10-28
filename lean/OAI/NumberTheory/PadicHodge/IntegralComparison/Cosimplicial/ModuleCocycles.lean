import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleComplex

/-! # Module Cocycles -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCocycles.Cup

noncomputable section

/-! The bilinear product on actual module-valued cocycles and its
vanishing on each boundary submodule. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleComplex

universe u v

variable {R : Type u} [CommRing R] (A : CosimplicialObject (CommAlgCat.{v} R))

def cycleCup (p q : ℕ) : Module.CochainClasses.cycles (ModuleComplex.complex A) p →ₗ[R] Module.CochainClasses.cycles (ModuleComplex.complex A) q →ₗ[R]
    Module.CochainClasses.cycles (ModuleComplex.complex A) (p + q) where
  toFun x :=
    { toFun := fun y => ⟨Cup.cup (ModuleComplex.ringObject A) x.1 y.1,
        (ModuleComplex.complex_d_apply A (p + q) _).trans
          (Cup.cup_isCocycle (ModuleComplex.ringObject A) x.1 y.1
            (ModuleComplex.cycle_differential A x) (ModuleComplex.cycle_differential A y))⟩
      map_add' := fun y z => Subtype.ext (Cup.cup_add_right (ModuleComplex.ringObject A) x.1 y.1 z.1)
      map_smul' := fun r y => Subtype.ext (ModuleComplex.cup_smul_right A r x.1 y.1) }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (Cup.cup_add_left (ModuleComplex.ringObject A) x.1 x'.1 y.1)
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (ModuleComplex.cup_smul_left A r x.1 y.1)

def cycleCupClass (p q : ℕ) : Module.CochainClasses.cycles (ModuleComplex.complex A) p →ₗ[R] Module.CochainClasses.cycles (ModuleComplex.complex A) q →ₗ[R]
    (ModuleComplex.complex A).homology (p + q) :=
  (cycleCup A p q).compr₂ (Module.CochainClasses.classMap (ModuleComplex.complex A) (p + q))

theorem cycleCupClass_boundary_left (p q : ℕ)
    (x : Module.CochainClasses.cycles (ModuleComplex.complex A) p) (y : Module.CochainClasses.cycles (ModuleComplex.complex A) q)
    (hx : x ∈ Module.CochainClasses.boundaries (ModuleComplex.complex A) p) : cycleCupClass A p q x y = 0 := by
  obtain ⟨b, hb⟩ := hx
  have hv : (ModuleComplex.complex A).d ((ComplexShape.up ℕ).prev p) p b = x.1 := congrArg Subtype.val hb
  have hva : ((Cup.complex (ModuleComplex.ringObject A)).sc p).f b = x.1 :=
    (ModuleComplex.d_apply_eq_additive A _ p b).symm.trans hv
  apply (Module.CochainClasses.classMap_eq_zero_iff (ModuleComplex.complex A) (p + q) (cycleCup A p q x y)).mpr
  apply (ModuleComplex.boundary_iff_additive A (p + q) _).mpr
  obtain ⟨z, hz⟩ := CupBoundaries.cup_boundary_left (ModuleComplex.ringObject A) p q b
    (ModuleComplex.additiveCycle A y)
  refine ⟨z, hz.trans ?_⟩
  exact congrArg (fun t : (ModuleComplex.ringObject A).obj ⦋p⦌ =>
    Cup.cup (ModuleComplex.ringObject A) (q := q) t y.1) hva

theorem cycleCupClass_boundary_right (p q : ℕ)
    (x : Module.CochainClasses.cycles (ModuleComplex.complex A) p) (y : Module.CochainClasses.cycles (ModuleComplex.complex A) q)
    (hy : y ∈ Module.CochainClasses.boundaries (ModuleComplex.complex A) q) : cycleCupClass A p q x y = 0 := by
  obtain ⟨b, hb⟩ := hy
  have hv : (ModuleComplex.complex A).d ((ComplexShape.up ℕ).prev q) q b = y.1 := congrArg Subtype.val hb
  have hva : ((Cup.complex (ModuleComplex.ringObject A)).sc q).f b = y.1 :=
    (ModuleComplex.d_apply_eq_additive A _ q b).symm.trans hv
  apply (Module.CochainClasses.classMap_eq_zero_iff (ModuleComplex.complex A) (p + q) (cycleCup A p q x y)).mpr
  apply (ModuleComplex.boundary_iff_additive A (p + q) _).mpr
  obtain ⟨z, hz⟩ := CupBoundaries.cup_boundary_right (ModuleComplex.ringObject A) p q
    (ModuleComplex.additiveCycle A x) b
  refine ⟨z, hz.trans ?_⟩
  exact congrArg (fun t : (ModuleComplex.ringObject A).obj ⦋q⦌ =>
    Cup.cup (ModuleComplex.ringObject A) (p := p) x.1 t) hva

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCocycles.Cup
