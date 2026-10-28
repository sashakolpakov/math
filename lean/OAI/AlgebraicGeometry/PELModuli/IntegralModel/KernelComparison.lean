import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Kernel Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.KernelComparison

noncomputable section

/-! The full scheme-theoretic kernel classifies maps annihilated by
the original morphism on every test scheme. These explicit pullback
identities are independent of arithmetic base expressions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme} {X C : Over S} [GrpObj C]

theorem kernel_inclusion_zero (f : X ⟶ C) : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ f = 1 := by
  change pullback.fst f η[C] ≫ f = toUnit (Picard.PoincareBundle.Kernel.Scheme.kernelObject f) ≫ η[C]
  exact (pullback.condition).trans
    (congrArg (fun a => a ≫ η[C]) (Subsingleton.elim _ _))

theorem kernel_inclusion_classifies (f : X ⟶ C) (T : Over S) (x : T ⟶ X) :
    x ≫ f = 1 ↔ ∃ z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f, z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = x := by
  constructor
  · intro h
    exact ⟨pullback.lift x (toUnit T) h, pullback.lift_fst _ _ _⟩
  · rintro ⟨z, rfl⟩
    rw [Category.assoc, kernel_inclusion_zero, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.KernelComparison
