import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Homology Specified Cycles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomologySpecifiedCycles

noncomputable section

/-! The homology object can be computed using any specified kernel of the outgoing differential and the cokernel of the incoming differential lifted to that kernel. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v
variable {V : Type u} [Category.{v} V] [Abelian V]

def homologySpecifiedCyclesIso (S : ShortComplex V)
    {Z : V} (i : Z ⟶ S.X₂) (wi : i ≫ S.g = 0)
    (hi : IsLimit (KernelFork.ofι i wi)) (a : S.X₁ ⟶ Z) (ha : a ≫ i = S.f) :
    S.homology ≅ cokernel a := by
  have hf : hi.lift (KernelFork.ofι S.f S.zero) = a := by
    apply Fork.IsLimit.hom_ext hi
    exact (Fork.IsLimit.lift_ι hi).trans ha.symm
  subst a
  let h : S.LeftHomologyData := {
    K := Z
    H := cokernel (hi.lift (KernelFork.ofι S.f S.zero))
    i := i
    π := cokernel.π (hi.lift (KernelFork.ofι S.f S.zero))
    wi := wi
    hi := hi
    wπ := cokernel.condition _
    hπ := cokernelIsCokernel _ }
  exact h.homologyIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomologySpecifiedCycles
