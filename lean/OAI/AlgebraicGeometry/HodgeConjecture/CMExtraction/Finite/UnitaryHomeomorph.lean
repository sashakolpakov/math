import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryInverse
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedControlledContinuity

/-! # Unitary Homeomorph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryHomeomorph.Approximation

noncomputable section

/-! The assembled completed unitary matrices and the actual local
restricted product have the same topology. The inverse is controlled by
the finitely many entries of a matrix and its inverse. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] {d : F}
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem globalUnitaryCoefficient_continuous (k : Bool × Bool × Fin 3 × Fin 3) :
    Continuous (UnitaryInverse.Approximation.globalUnitaryCoefficient F H k) := by
  have hm : Continuous (fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H) =>
      (if k.1 then g.val.inv else g.val.val : Matrix (Fin 3) (Fin 3)
        (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)))) := by
    cases hk : k.1
    · simpa only [hk, Bool.false_eq_true, ↓reduceIte] using
        (show Continuous (fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H) =>
          (g.val.val : Matrix (Fin 3) (Fin 3)
            (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)))) from
          Units.continuous_val.comp continuous_subtype_val)
    · simpa only [hk, ↓reduceIte] using
        (show Continuous (fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H) =>
          (g.val.inv : Matrix (Fin 3) (Fin 3)
            (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)))) from
          Units.continuous_coe_inv.comp continuous_subtype_val)
  have he := (continuous_apply k.2.2.2).comp ((continuous_apply k.2.2.1).comp hm)
  unfold UnitaryInverse.Approximation.globalUnitaryCoefficient
  cases hc : k.2.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im _).comp he
  · simp only [↓reduceIte]
    exact (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re _).comp he

theorem finiteUnitaryInverse_continuous : Continuous (UnitaryInverse.Approximation.finiteUnitaryInverse F H) := by
  refine RestrictedControlledContinuity.Approximation.continuous_restricted_of_finite_controls
    (X := RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H))
    (G := fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))
    (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v) : Set _))
    (R := fun (_ : Bool × Bool × Fin 3 × Fin 3) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) => v.adicCompletion F)
    (fun _ v => (v.adicCompletionIntegers F : Set _))
    (fun _ v => RepresentationTheory.Theta.Adelic.IntegralTopology.localIntegerRing_open F (.inr v))
    (UnitaryInverse.Approximation.globalUnitaryCoefficient F H) (globalUnitaryCoefficient_continuous F H)
    (fun g => UnitaryInverse.Approximation.finiteUnitaryInverse F H g) (fun v => (UnitaryInverse.Approximation.finiteGlobalLocal F H v).continuous) ?_
  intro g v hg
  exact UnitaryInverse.Approximation.finiteGlobalLocal_integral F H v g hg

def finiteUnitaryCompletedHomeomorph : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H ≃ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H) where
  __ := UnitaryInverse.Approximation.finiteUnitaryCompletedEquiv F H
  continuous_toFun := (UnitaryDet.Approximation.finiteAdelicUnitary F H).continuous
  continuous_invFun := finiteUnitaryInverse_continuous F H

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryHomeomorph.Approximation
