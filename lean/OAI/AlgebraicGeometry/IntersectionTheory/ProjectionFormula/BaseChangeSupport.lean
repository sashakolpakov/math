import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
import Mathlib.RingTheory.Spectrum.Prime.Module

/-! # Base Change Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BaseChangeSupport

noncomputable section

/-! Every prime supporting the base change of a finite module maps
to the support of the original module. No flatness is needed. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat.{u} R)

theorem annihilator (r : R) (hr : r ∈ Module.annihilator R M) :
    algebraMap R S r ∈ Module.annihilator S ((Flat.Extension.baseChange R S).obj M) := by
  apply Module.mem_annihilator.mpr
  change ∀ x : S ⊗[R] M, algebraMap R S r • x = 0
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Module.mem_annihilator.mp hr m, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

theorem mem_image [Module.Finite R M] (p : PrimeSpectrum S)
    (hp : p ∈ Module.support S ((Flat.Extension.baseChange R S).obj M)) :
    PrimeSpectrum.comap (algebraMap R S) p ∈ Module.support R M := by
  apply Module.mem_support_iff_of_finite.mpr
  intro r hr
  exact (Module.annihilator_le_of_mem_support hp) (BaseChangeSupport.annihilator R S M r hr)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BaseChangeSupport
