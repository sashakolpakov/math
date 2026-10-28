import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Chain Zero Cokernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ChainZeroCokernel

noncomputable section

/-! Degree-zero chain homology is identified with a specified cokernel
of the degree-one differential. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

def iso (K : ChainComplex C ℕ) {X : C} (p : K.X 0 ⟶ X)
    (wp : K.d 1 0 ≫ p = 0) (hp : (ShortComplex.mk (K.d 1 0) p wp).Exact) [Epi p] :
    K.homology 0 ≅ X :=
  K.homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    (ShortComplex.RightHomologyData.ofIsColimitCokernelCofork (K.sc' 1 0 0)
      (K.shape 0 0 (by simp)) (CokernelCofork.ofπ p wp) hp.gIsCokernel).homologyIso

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ChainZeroCokernel
