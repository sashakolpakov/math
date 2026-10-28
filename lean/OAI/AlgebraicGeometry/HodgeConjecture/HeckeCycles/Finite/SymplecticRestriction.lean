import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RingSymplecticPairing
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.RationalLinearity

/-! # Symplectic Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticRestriction.CM

noncomputable section

/-! Restriction of scalars gives an actual symplectic representation over
the rational finite adeles, in the proved trace-dual phase coordinates. -/

open scoped Classical _root_.NumberField _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def linear (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) :
    ((AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[ℚ] ((AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) := by
  let a : ((Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃L[ℚ]
      ((Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
    RingSymplecticPairing.CM.rationalContinuousLinearEquiv
      (I := Fin N) (R := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) g
  exact (TracePhase.CM.coordinates F N).symm.trans (a.trans (TracePhase.CM.coordinates F N))

theorem linear_pairing (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))
    (x y : (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    TracePhase.CM.pairing (linear F N g x) (linear F N g y) = TracePhase.CM.pairing x y := by
  change TracePhase.CM.pairing (TracePhase.CM.coordinates F N (g.val *ᵥ (TracePhase.CM.coordinates F N).symm x))
    (TracePhase.CM.coordinates F N (g.val *ᵥ (TracePhase.CM.coordinates F N).symm y)) = _
  rw [TracePhase.CM.coordinates_pairing, RingSymplecticPairing.CM.preserves,
    ← TracePhase.CM.coordinates_pairing, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

def matrix (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) :
    Matrix (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  RationalLinearity.CM.matrix (linear F N g).toLinearMap (linear F N g).continuous

theorem matrix_apply (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))
    (x : (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : matrix F N g *ᵥ x = linear F N g x :=
  RationalLinearity.CM.matrix_apply _ _ x

theorem linear_one (x : (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : linear F N 1 x = x := by
  change TracePhase.CM.coordinates F N ((1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) *ᵥ
    (TracePhase.CM.coordinates F N).symm x) = x
  rw [Matrix.one_mulVec, ContinuousLinearEquiv.apply_symm_apply]

theorem linear_mul (g h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))
    (x : (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : linear F N (g * h) x = linear F N g (linear F N h x) := by
  change TracePhase.CM.coordinates F N ((g.val * h.val) *ᵥ (TracePhase.CM.coordinates F N).symm x) =
    TracePhase.CM.coordinates F N (g.val *ᵥ (TracePhase.CM.coordinates F N).symm
      (TracePhase.CM.coordinates F N (h.val *ᵥ (TracePhase.CM.coordinates F N).symm x)))
  rw [ContinuousLinearEquiv.symm_apply_apply, ← Matrix.mulVec_mulVec]

def restriction : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (AdelicTestCoordinates.CM.Index F N) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf where
  toFun g := ⟨matrix F N g, RingSymplecticPairing.CM.matrix_symplectic
    (I := AdelicTestCoordinates.CM.Index F N) (R := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (matrix F N g) (by
    intro x y
    rw [matrix_apply, matrix_apply]
    exact linear_pairing F N g x y)⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change matrix F N 1 *ᵥ x = (1 : Matrix (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ x
    rw [matrix_apply, linear_one, Matrix.one_mulVec]
  map_mul' g h := by
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change matrix F N (g * h) *ᵥ x = (matrix F N g * matrix F N h) *ᵥ x
    rw [← Matrix.mulVec_mulVec, matrix_apply, matrix_apply, matrix_apply, linear_mul]

theorem restriction_apply (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))
    (x : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (restriction F N g).val *ᵥ TracePhase.CM.coordinates F N x = TracePhase.CM.coordinates F N (g.val *ᵥ x) := by
  rw [show (restriction F N g).val = matrix F N g from rfl, matrix_apply]
  change TracePhase.CM.coordinates F N (g.val *ᵥ (TracePhase.CM.coordinates F N).symm (TracePhase.CM.coordinates F N x)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticRestriction.CM
