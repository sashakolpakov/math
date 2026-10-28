import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap

/-! # Completion Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.CompletionMap.SemilinearCompletionMap

noncomputable section

/-! # Semilinear chain maps pass through integral adic completion -/

open _root_.CategoryTheory

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (σ : R →+* S) (I : Ideal R) (J : Ideal S) (h : Ideal.map σ I ≤ J)
  {C : CochainComplex (ModuleCat.{u} R) ℕ} {D : CochainComplex (ModuleCat.{u} S) ℕ}
  (f : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map σ C D)

abbrev completion (C : CochainComplex (ModuleCat.{u} R) ℕ) :=
  ((NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear.functor I).mapHomologicalComplex (.up ℕ)).obj C

def map : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map σ (completion I C) (completion J D) where
  f n := NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.map σ I J h (f.f n)
  comm i j x := by
    apply AdicCompletion.ext
    intro n
    change NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.reduce σ I J h (f.f j) n
        ((C.d i j).hom.reduceModIdeal (I ^ n) (x.val n)) =
      (D.d i j).hom.reduceModIdeal (J ^ n)
        (NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.reduce σ I J h (f.f i) n (x.val n))
    generalize x.val n = q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      change Submodule.Quotient.mk (f.f j ((C.d i j).hom y)) =
        Submodule.Quotient.mk ((D.d i j).hom (f.f i y))
      exact congrArg (Submodule.Quotient.mk (p := J ^ n • (⊤ : Submodule S (D.X j)))) (f.comm i j y)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.CompletionMap.SemilinearCompletionMap
