import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTrace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TracePhaseCoordinates

/-! # Trace Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePairing.CM

noncomputable section

/-! Exact position/momentum pairing in the finite-adelic trace coordinates. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def position : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃L[ℚ] (AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicLinearEquiv F (Fin N)

def momentum : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) →ₗ[ℚ] (AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toFun y i := AdelicTrace.CM.trace F
    (y i.1 * algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (integralBasis F i.2))
  map_add' x y := by funext i; simp only [Pi.add_apply, add_mul, map_add]
  map_smul' c y := by
    funext i
    simp only [Pi.smul_apply, smul_mul_assoc, map_smul, RingHom.id_apply]

theorem momentum_continuous : Continuous (momentum F N) := by
  apply continuous_pi
  intro i
  exact (AdelicTrace.CM.trace_continuous F).comp
    ((continuous_apply i.1).mul continuous_const)

theorem position_rational (x : Fin N → F) :
    position F N (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) x) :=
  CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicLinearEquiv_rational F (Fin N) x

theorem momentum_rational (x : Fin N → F) :
    momentum F N (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (TracePhaseCoordinates.CM.momentum F N x) := by
  funext i
  change AdelicTrace.CM.trace F
    (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (x i.1) * algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (integralBasis F i.2)) =
      algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ((integralBasis F).traceDual.repr (x i.1) i.2)
  rw [← map_mul, AdelicTrace.CM.trace_rational,
    Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]

theorem pairing (x y : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∑ i, position F N x i * momentum F N y i =
      AdelicTrace.CM.trace F (∑ j, x j * y j) := by
  have hleft : Continuous (fun p : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) × (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) =>
      ∑ i, position F N p.1 i * momentum F N p.2 i) := by
    apply continuous_finsetSum Finset.univ
    intro i _
    exact ((continuous_apply i).comp ((position F N).continuous.comp continuous_fst)).mul
      ((continuous_apply i).comp ((momentum_continuous F N).comp continuous_snd))
  have hright : Continuous (fun p : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) × (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) =>
      AdelicTrace.CM.trace F (∑ j, p.1 j * p.2 j)) :=
    (AdelicTrace.CM.trace_continuous F).comp
      (continuous_finsetSum Finset.univ fun j _ =>
        ((continuous_apply j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))
  have h := (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.denseRange_finiteRationalPosition (F := F) (ι := Fin N)).prodMap
    (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.denseRange_finiteRationalPosition (F := F) (ι := Fin N))
  have he := h.equalizer hleft hright
  apply congrFun (he ?_) (x, y)
  funext p
  change (∑ i, position F N (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition p.1) i *
    momentum F N (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition p.2) i) =
      AdelicTrace.CM.trace F
        (∑ j, RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition p.1 j * RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition p.2 j)
  rw [position_rational, momentum_rational]
  change (∑ i, algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) p.1 i) *
    algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (TracePhaseCoordinates.CM.momentum F N p.2 i)) =
      AdelicTrace.CM.trace F
        (∑ j, algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (p.1 j) * algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (p.2 j))
  simp only [← map_mul, ← map_sum]
  rw [AdelicTrace.CM.trace_rational, TracePhaseCoordinates.CM.position_momentum_pairing]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePairing.CM
