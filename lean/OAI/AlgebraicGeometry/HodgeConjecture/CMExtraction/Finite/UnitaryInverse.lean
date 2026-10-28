import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryDet
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecialUnitaryBaseChange
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalUnitary

/-! # Unitary Inverse -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryInverse.Approximation

noncomputable section

/-! Evaluate a unitary matrix over the completed quadratic algebra at
all finite places. Its entries and inverse entries are integral at almost
all places, so it defines the actual restricted unitary adele. -/

open scoped Classical _root_.NumberField
open Filter

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalUnitary
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] {d : F}
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem finiteQuadraticEvaluation_continuous (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    Continuous (UnitaryDet.Approximation.finiteQuadraticEvaluation F d v) := by
  rw [RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
  exact ⟨(RestrictedProduct.continuous_eval v).comp (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re _),
    (RestrictedProduct.continuous_eval v).comp (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im _)⟩

def finiteGlobalLocal (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H) →ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) :=
  (⟨(CM.UnitaryPresentation.Quadratic.unitaryFormCongr _ _ (UnitaryDet.Approximation.finiteQuadraticEvaluation_matrix F d v H.val)).toMonoidHom,
    Quaternion.LocalUnitary.unitaryFormCongr_continuous _ _ (UnitaryDet.Approximation.finiteQuadraticEvaluation_matrix F d v H.val)⟩ :
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU _ →ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU _).comp
    (SpecialUnitaryBaseChange.Approximation.specialUnitaryBaseChangeContinuous (UnitaryDet.Approximation.finiteQuadraticEvaluation F d v)
      (UnitaryDet.Approximation.finiteQuadraticEvaluation_star F d v) _ (finiteQuadraticEvaluation_continuous F v))

theorem finiteGlobalLocal_matrix (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H)) :
    (finiteGlobalLocal F H v g).val.val = g.val.val.map (UnitaryDet.Approximation.finiteQuadraticEvaluation F d v) := rfl

def globalUnitaryCoefficient (k : Bool × Bool × Fin 3 × Fin 3)
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H)) : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F :=
  let M := if k.1 then g.val.inv else g.val.val
  if k.2.1 then (M k.2.2.1 k.2.2.2).re else (M k.2.2.1 k.2.2.2).im

theorem finiteGlobalLocal_integral (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H))
    (hg : ∀ k, globalUnitaryCoefficient F H k g v ∈ v.adicCompletionIntegers F) :
    finiteGlobalLocal F H v g ∈ RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v) := by
  constructor
  · intro i j
    apply RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff
    · exact hg ⟨false, true, i, j⟩
    · exact hg ⟨false, false, i, j⟩
  · intro i j
    apply RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff
    · exact hg ⟨true, true, i, j⟩
    · exact hg ⟨true, false, i, j⟩

theorem finiteGlobalLocal_eventually_integral (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H)) :
    ∀ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F in cofinite, finiteGlobalLocal F H v g ∈ RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v) := by
  have hg : ∀ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F in cofinite,
      ∀ k, globalUnitaryCoefficient F H k g v ∈ v.adicCompletionIntegers F :=
    eventually_all.mpr (fun k => (globalUnitaryCoefficient F H k g).property)
  exact hg.mono (fun v hv => finiteGlobalLocal_integral F H v g hv)

def finiteUnitaryInverse : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H) →* RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H where
  toFun g := ⟨fun v => finiteGlobalLocal F H v g, finiteGlobalLocal_eventually_integral F H g⟩
  map_one' := by apply RestrictedProduct.ext; intro v; exact map_one (finiteGlobalLocal F H v)
  map_mul' g h := by apply RestrictedProduct.ext; intro v; exact map_mul (finiteGlobalLocal F H v) g h

theorem finiteUnitaryInverse_left (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) :
    finiteUnitaryInverse F H (UnitaryDet.Approximation.finiteAdelicUnitary F H g) = g := by
  apply RestrictedProduct.ext
  intro v
  apply Subtype.ext
  apply Units.ext
  exact UnitaryDet.Approximation.finiteSUQuadraticMatrix_evaluation F H g v

theorem finiteUnitaryInverse_right (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H)) :
    UnitaryDet.Approximation.finiteAdelicUnitary F H (finiteUnitaryInverse F H g) = g := by
  apply Subtype.ext
  apply Units.ext
  apply UnitaryDet.Approximation.finiteQuadraticMatrix_ext F d
  intro v
  exact (UnitaryDet.Approximation.finiteSUQuadraticMatrix_evaluation F H (finiteUnitaryInverse F H g) v).trans
    (finiteGlobalLocal_matrix F H v g)

def finiteUnitaryCompletedEquiv : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryDet.Approximation.finiteHermitianMatrix F H) where
  toFun := UnitaryDet.Approximation.finiteAdelicUnitary F H
  invFun := finiteUnitaryInverse F H
  left_inv := finiteUnitaryInverse_left F H
  right_inv := finiteUnitaryInverse_right F H
  map_mul' := map_mul (UnitaryDet.Approximation.finiteAdelicUnitary F H)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryInverse.Approximation
