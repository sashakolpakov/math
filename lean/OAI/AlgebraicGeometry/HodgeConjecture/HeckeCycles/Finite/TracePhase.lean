import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MomentumEquiv

/-! # Trace Phase -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase.CM

/-! Actual continuous phase coordinates in the oscillator's prescribed
momentum/position order, with the exact traced alternating pairing. -/

open scoped Classical _root_.NumberField _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

def sumCoordinates (R S I : Type*) [Semiring R] [AddCommMonoid S] [Module R S]
    [TopologicalSpace S] : ((I ⊕ I) → S) ≃L[R] ((I → S) × (I → S)) where
  toLinearEquiv := LinearEquiv.sumArrowLequivProdArrow I I R S
  continuous_toFun := by
    change Continuous (fun f : (I ⊕ I) → S => (fun i => f (Sum.inl i), fun i => f (Sum.inr i)))
    exact (continuous_pi fun i => continuous_apply (Sum.inl i : I ⊕ I)).prodMk
      (continuous_pi fun i => continuous_apply (Sum.inr i : I ⊕ I))
  continuous_invFun := by
    change Continuous (fun p : (I → S) × (I → S) => Sum.elim p.1 p.2)
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact (continuous_apply i).comp continuous_fst
    | inr i => exact (continuous_apply i).comp continuous_snd

def pairing {I R : Type*} [Fintype I] [CommRing R] (x y : (I ⊕ I) → R) : R :=
  ∑ i, (x (.inl i) * y (.inr i) - y (.inl i) * x (.inr i))

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def coordinates : ((Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃L[ℚ]
    ((AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  (sumCoordinates ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (Fin N)).trans
    ((ContinuousLinearEquiv.prodComm ℚ _ _).trans
      ((MomentumEquiv.CM.phase F N).trans (sumCoordinates ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (AdelicTestCoordinates.CM.Index F N)).symm))

theorem coordinates_left (x : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (i : AdelicTestCoordinates.CM.Index F N) :
    coordinates F N x (.inl i) = TracePairing.CM.momentum F N (fun j => x (.inr j)) i :=
  congrFun (MomentumEquiv.CM.equivalence_apply F N (fun j => x (.inr j))) i

theorem coordinates_right (x : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (i : AdelicTestCoordinates.CM.Index F N) :
    coordinates F N x (.inr i) = TracePairing.CM.position F N (fun j => x (.inl j)) i := rfl

theorem coordinates_pairing (x y : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    pairing (coordinates F N x) (coordinates F N y) = -AdelicTrace.CM.trace F (pairing x y) := by
  simp only [pairing, coordinates_left, coordinates_right, Finset.sum_sub_distrib]
  have hx : (∑ i, TracePairing.CM.momentum F N (fun j => x (.inr j)) i *
      TracePairing.CM.position F N (fun j => y (.inl j)) i) =
      AdelicTrace.CM.trace F (∑ j, y (.inl j) * x (.inr j)) := by
    rw [show (∑ i, TracePairing.CM.momentum F N (fun j => x (.inr j)) i *
        TracePairing.CM.position F N (fun j => y (.inl j)) i) =
        ∑ i, TracePairing.CM.position F N (fun j => y (.inl j)) i *
          TracePairing.CM.momentum F N (fun j => x (.inr j)) i from
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
    exact TracePairing.CM.pairing F N _ _
  have hy : (∑ i, TracePairing.CM.momentum F N (fun j => y (.inr j)) i *
      TracePairing.CM.position F N (fun j => x (.inl j)) i) =
      AdelicTrace.CM.trace F (∑ j, x (.inl j) * y (.inr j)) := by
    rw [show (∑ i, TracePairing.CM.momentum F N (fun j => y (.inr j)) i *
        TracePairing.CM.position F N (fun j => x (.inl j)) i) =
        ∑ i, TracePairing.CM.position F N (fun j => x (.inl j)) i *
          TracePairing.CM.momentum F N (fun j => y (.inr j)) i from
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
    exact TracePairing.CM.pairing F N _ _
  rw [hx, hy, map_sub]
  ring

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase.CM.Rational

/-! The finite trace coordinates agree exactly with the rational
trace-dual momentum and integral-basis position coordinates. -/

open scoped Classical _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def rational (x : (Fin N ⊕ Fin N) → F) : (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → ℚ :=
  Sum.elim (TracePhaseCoordinates.CM.momentum F N (fun i => x (.inr i)))
    (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralPositionCoordinates F (Fin N) (fun i => x (.inl i)))

theorem coordinates_rational (x : (Fin N ⊕ Fin N) → F) :
    coordinates F N (fun i => algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (x i)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (rational F N x) := by
  funext i
  cases i with
  | inl i =>
      rw [coordinates_left]
      exact congrFun (TracePairing.CM.momentum_rational F N (fun j => x (.inr j))) i
  | inr i =>
      rw [coordinates_right]
      exact congrFun (TracePairing.CM.position_rational F N (fun j => x (.inl j))) i

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase.CM.Rational

end

end OAI
