import OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
import OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

/-! # Unitary Entries -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryEntries.Approximation

noncomputable section

/-! The real and imaginary entries of an actual finite unitary adele
are number-field finite adeles, continuously in the restricted topology. -/

open scoped Classical _root_.NumberField
open Filter

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

variable (F : Type) [Field F] [NumberField F] {n : ℕ} {d : F}
  (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

def localSUCoordinate (c : Bool) (i j : Fin n) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v))) : v.adicCompletion F :=
  if c then (g.val.val i j).re else (g.val.val i j).im

theorem localSUCoordinate_continuous (c : Bool) (i j : Fin n) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    Continuous (localSUCoordinate F H c i j v) := by
  have hmatrix : Continuous (fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) =>
      (g.val.val : Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v)))) :=
    (show Continuous (fun u : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v)))ˣ => u.val)
      from Units.continuous_val).comp continuous_subtype_val
  have hm : Continuous (fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) => g.val.val i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hmatrix)
  cases c
  · exact (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im _).comp hm
  · exact (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re _).comp hm

theorem localSUCoordinate_eventually_integral (c : Bool) (i j : Fin n) :
    ∀ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F in cofinite,
      Set.MapsTo (localSUCoordinate F H c i j v)
        (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v)) (v.adicCompletionIntegers F) := by
  filter_upwards [Sum.inr_injective.tendsto_cofinite.eventually (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d)]
    with v hv
  intro g hg
  have hm : g.val.val i j ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) := hg.1 i j
  have hc := (RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients.quadraticOrder_coefficients F d (.inr v) hv _).mp hm
  cases c
  · exact hc.2
  · exact hc.1

def finiteSUCoordinate (c : Bool) (i j : Fin n) : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F :=
  RestrictedProduct.map (C := fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F =>
    (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v) : Set (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))))
    (D := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (localSUCoordinate F H c i j) (localSUCoordinate_eventually_integral F H c i j)

theorem finiteSUCoordinate_apply (c : Bool) (i j : Fin n) (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    finiteSUCoordinate F H c i j g v = localSUCoordinate F H c i j v (g v) := rfl

theorem finiteSUCoordinate_continuous (c : Bool) (i j : Fin n) :
    Continuous (finiteSUCoordinate F H c i j) :=
  RestrictedProduct.mapAlong_continuous
    (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))
    (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => v.adicCompletion F)
    id tendsto_id (localSUCoordinate F H c i j)
    (localSUCoordinate_eventually_integral F H c i j)
    (localSUCoordinate_continuous F H c i j)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryEntries.Approximation
