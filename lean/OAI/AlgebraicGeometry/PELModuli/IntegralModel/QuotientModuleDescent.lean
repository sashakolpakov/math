import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Hom
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Quotient Module Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientModuleDescent

noncomputable section

/-! Actual module descent along a surjective ring map, with its canonical
extension-restriction unit proved invertible. -/

open _root_.CategoryTheory

universe u v w

theorem surjectiveRingHom_restrictScalars_full
    {R : Type u} {A : Type v} [Ring R] [Ring A]
    (f : R →+* A) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{w} f).Full := by
  constructor
  intro M N g
  refine ⟨ModuleCat.ofHom
    { g.hom.toAddHom with map_smul' := ?_ }, ?_⟩
  · intro a m
    obtain ⟨r, rfl⟩ := hf a
    exact g.hom.map_smul r m
  · ext m
    rfl

theorem exists_module_descent_of_kernel_annihilates
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f)
    (M : ModuleCat.{w} R) (h : RingHom.ker f ≤ Module.annihilator R M) :
    ∃ N : ModuleCat.{w} A, Nonempty ((ModuleCat.restrictScalars f).obj N ≅ M) := by
  have hk : RingHom.ker f ≤ RingHom.ker (Module.toAddMonoidEnd R M) := by
    intro r hr
    apply RingHom.mem_ker.mpr
    ext m
    exact Module.mem_annihilator.mp (h hr) m
  let a : {g : R →+* AddMonoid.End M // RingHom.ker f ≤ RingHom.ker g} :=
    ⟨Module.toAddMonoidEnd R M, hk⟩
  let ρ := f.liftOfSurjective hf a
  have hρ : ρ.comp f = Module.toAddMonoidEnd R M :=
    congrArg Subtype.val ((f.liftOfSurjective hf).symm_apply_apply a)
  let : Module A M := Module.compHom M ρ
  let e : (ModuleCat.restrictScalars f).obj (ModuleCat.of A M) ≃ₗ[R] M :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        let m' : M := m
        change ρ (f r) m' = r • m'
        exact congrArg (fun g : AddMonoid.End M => g m') (RingHom.congr_fun hρ r) }
  exact ⟨ModuleCat.of A M, ⟨e.toModuleIso⟩⟩

theorem quotientModule_unit_isIso
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) (h : RingHom.ker f ≤ Module.annihilator R M) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj f).unit.app M) := by
  have := surjectiveRingHom_restrictScalars_full.{u, u, u} f hf
  obtain ⟨N, ⟨e⟩⟩ := exists_module_descent_of_kernel_annihilates f hf M h
  exact (ModuleCat.extendRestrictScalarsAdj f).isIso_unit_app_of_iso e.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientModuleDescent
