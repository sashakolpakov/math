import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Ideal.Maps

/-! # Retract Module Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RetractModuleLength.Constructions

noncomputable section

/-! A module annihilated by the kernel of an algebra retraction has
the same length over the algebra and over its retract. This retains
the actual restricted action and allows infinite lengths. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (μ : A →ₐ[R] R) (M : ModuleCat.{u} A)

local instance restrictedAlgebraModule : Module A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
  inferInstanceAs (Module A M)

theorem factor_smul (h : RingHom.ker μ.toRingHom ≤ Module.annihilator A M)
    (a : A) (x : (ModuleCat.restrictScalars (algebraMap R A)).obj M) :
    a • x = μ a • x := by
  have hk : a - algebraMap R A (μ a) ∈ RingHom.ker μ.toRingHom := by
    change μ (a - algebraMap R A (μ a)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hx := Module.mem_annihilator.mp (h hk) (show M from x)
  rw [sub_smul, sub_eq_zero] at hx
  exact hx

theorem length_eq (h : RingHom.ker μ.toRingHom ≤ Module.annihilator A M) :
    Module.length A M = Module.length R ((ModuleCat.restrictScalars (algebraMap R A)).obj M) := by
  let : Algebra A R := μ.toRingHom.toAlgebra
  let : IsScalarTower A R ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
    IsScalarTower.of_algebraMap_smul (fun a x => (factor_smul R A μ M h a x).symm)
  apply Module.length_eq_of_surjective (R := R) (S := A)
    (M := (ModuleCat.restrictScalars (algebraMap R A)).obj M)
  intro r
  refine ⟨algebraMap R A r, ?_⟩
  exact μ.commutes r

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RetractModuleLength.Constructions
