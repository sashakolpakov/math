import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Homology Kernel Cokernel -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologyKernelCokernel

noncomputable section

/-! Compute the homology of a short complex from any actual cokernel
of its first differential and the induced map out of that cokernel. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

def homologyIsoKernel (S : ShortComplex C) (Q : C) (p : S.X₂ ⟶ Q)
    (wp : S.f ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p wp))
    (g : Q ⟶ S.X₃) (hg : p ≫ g = S.g) : S.homology ≅ kernel g := by
  have hdesc : hp.desc (CokernelCofork.ofπ S.g S.zero) = g := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc]
    exact hg.symm
  subst g
  let h : S.RightHomologyData :=
    { Q := Q
      H := kernel (hp.desc (CokernelCofork.ofπ S.g S.zero))
      p := p
      ι := kernel.ι _
      wp := wp
      hp := hp
      wι := kernel.condition _
      hι := kernelIsKernel _ }
  exact h.homologyIso

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologyKernelCokernel
