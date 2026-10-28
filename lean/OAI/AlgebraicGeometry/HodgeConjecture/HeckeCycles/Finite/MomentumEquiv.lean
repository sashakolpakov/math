import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePairing
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.RationalSubstitution

/-! # Momentum Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MomentumEquiv.CM

noncomputable section

/-! The actual finite momentum coordinates form a continuous linear
equivalence, obtained from the trace-dual rational basis change. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.RationalSubstitution.TestTransport

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePairing.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def rationalChange : (AdelicTestCoordinates.CM.Index F N → ℚ) ≃ₗ[ℚ] (AdelicTestCoordinates.CM.Index F N → ℚ) :=
  (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N)).symm.trans (TracePhaseCoordinates.CM.momentum F N)

def homeomorph : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ (AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  (TracePairing.CM.position F N).toHomeomorph.trans (CMExtraction.Finite.RationalSubstitution.TestTransport.finitePositionHomeomorph (rationalChange F N))

theorem homeomorph_eq (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : homeomorph F N x = TracePairing.CM.momentum F N x := by
  have he : (homeomorph F N : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) → (AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) =
      TracePairing.CM.momentum F N := by
    apply (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.denseRange_finiteRationalPosition (F := F) (ι := Fin N)).equalizer
      (homeomorph F N).continuous (TracePairing.CM.momentum_continuous F N)
    funext y
    change CMExtraction.Finite.RationalSubstitution.TestTransport.finitePositionHomeomorph (rationalChange F N) (TracePairing.CM.position F N (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition y)) =
      TracePairing.CM.momentum F N (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition y)
    rw [TracePairing.CM.position_rational, CMExtraction.Finite.RationalSubstitution.TestTransport.finitePositionHomeomorph_rational, TracePairing.CM.momentum_rational]
    apply congrArg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal
    exact congrArg (TracePhaseCoordinates.CM.momentum F N)
      ((CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N)).symm_apply_apply y)
  exact congrFun he x

def equivalence : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃L[ℚ] (AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toLinearEquiv :=
    { toEquiv := (homeomorph F N).toEquiv
      map_add' := by
        intro x y
        change homeomorph F N (x + y) = homeomorph F N x + homeomorph F N y
        rw [homeomorph_eq, homeomorph_eq, homeomorph_eq, map_add]
      map_smul' := by
        intro c x
        change homeomorph F N (c • x) = c • homeomorph F N x
        rw [homeomorph_eq, homeomorph_eq, map_smul] }
  continuous_toFun := (homeomorph F N).continuous
  continuous_invFun := (homeomorph F N).symm.continuous

theorem equivalence_apply (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : equivalence F N x = TracePairing.CM.momentum F N x :=
  homeomorph_eq F N x

def phase : ((Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) × (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) ≃L[ℚ]
    ((AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) × (AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) :=
  (equivalence F N).prodCongr (TracePairing.CM.position F N)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MomentumEquiv.CM
