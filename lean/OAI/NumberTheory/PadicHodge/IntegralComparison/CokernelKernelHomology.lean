import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Cokernel Kernel Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CokernelKernelHomology

noncomputable section

/-! A concrete computation of short-complex homology from a cokernel of
the first map and a kernel of the resulting map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex C) {Q H : C} (p : S.X₂ ⟶ Q) (a : Q ⟶ S.X₃) (ι : H ⟶ Q)
  (wp : S.f ≫ p = 0) (hp : (ShortComplex.mk S.f p wp).Exact) [Epi p]
  (wι : ι ≫ a = 0) (hι : (ShortComplex.mk ι a wι).Exact) [Mono ι]
  (fac : p ≫ a = S.g)

include fac in
theorem desc_eq : hp.gIsCokernel.desc (CokernelCofork.ofπ S.g S.zero) = a := by
  apply (cancel_epi p).mp
  exact (hp.g_desc S.g S.zero).trans fac.symm

def data : S.RightHomologyData where
  Q := Q
  H := H
  p := p
  ι := ι
  wp := wp
  hp := hp.gIsCokernel
  wι := by rw [desc_eq S p a wp hp fac]; exact wι
  hι := by
    have ha := desc_eq S p a wp hp fac
    subst a
    exact hι.fIsKernel

def iso : S.homology ≅ H :=
  (data S p a ι wp hp wι hι fac).homologyIso

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CokernelKernelHomology
