import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.QuadraticBare
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe

/-! # Integral Vacuum -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare

/-! Lower unipotents have actual lifts to the finite bare group by
Fourier conjugation of the constructed quadratic lifts. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.QuadraticBare.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Normal

variable {I : Type*} [Fintype I]

def lower (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := by
  refine ⟨Matrix.fromBlocks 1 0 B 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hB.eq]

theorem lower_matrix (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    (FourierHeisenberg.CM.weyl (I := I))⁻¹ * RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-B) hB.neg *
      FourierHeisenberg.CM.weyl = lower B hB := by
  apply Subtype.ext
  change ((FourierHeisenberg.CM.weyl (I := I))⁻¹).val *
    (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-B) hB.neg).val * (FourierHeisenberg.CM.weyl (I := I)).val = _
  rw [SymplecticGroup.coe_inv]
  simp [FourierHeisenberg.CM.weyl, RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper, lower, Matrix.J,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

def lowerLift (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) : BareNe.CM.Group.BareGroup (I := I) := by
  refine ⟨FiniteOscillator.CM.fourierOscillator⁻¹ * Quadratic.CM.quadraticOscillator (-B) hB.neg * FiniteOscillator.CM.fourierOscillator, ?_⟩
  have h := (BareNe.CM.Normal.bare_normal (I := I)).conj_mem (Quadratic.CM.quadraticOscillator (-B) hB.neg)
    (QuadraticBare.CM.quadratic_mem (-B) hB.neg) (FiniteOscillator.CM.fourierOscillator⁻¹)
  simpa only [inv_inv] using h

theorem lowerLift_projection (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    BareNe.CM.Group.bareProjection (lowerLift B hB) = lower B hB := by
  change FiniteOscillator.CM.projection (FiniteOscillator.CM.fourierOscillator⁻¹ * Quadratic.CM.quadraticOscillator (-B) hB.neg * FiniteOscillator.CM.fourierOscillator) = _
  rw [map_mul, map_mul, map_inv]
  exact lower_matrix B hB

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM

/-! Exact fixation of the finite integral lattice vector by Fourier
and by upper/lower operators with half-integral coefficients. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM.Equiv
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare
variable {I : Type*} [Fintype I]

omit [Fintype I] in
theorem finiteLattice_one : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) 1 one_ne_zero = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.toAddSubgroup := by
  ext x
  simp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff, inv_one, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_one, Subring.mem_toAddSubgroup]

omit [Fintype I] in
theorem latticeIndicator_one : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator (ι := I) 1 one_ne_zero = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator := by
  funext x
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator, finiteLattice_one]
  rfl

theorem fourier_vacuum : FourierHeisenberg.CM.Equiv.fourierEquiv (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  apply Subtype.ext
  funext x
  rw [FourierHeisenberg.CM.Equiv.fourierEquiv_apply]
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I)
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x
  rw [← latticeIndicator_one, Constructed.FiniteFourier.CM.latticeIndicator_fourier]
  simp only [inv_one, latticeIndicator_one, finiteLattice_one]
  rw [Subring.coe_toAddSubgroup]
  rw [Constructed.FiniteMeasure.CM.integral_real_volume]
  simp

theorem inverse_fourier_vacuum :
    FourierHeisenberg.CM.Equiv.fourierEquiv.symm (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  apply FourierHeisenberg.CM.Equiv.fourierEquiv.injective
  rw [LinearEquiv.apply_symm_apply, fourier_vacuum]

def HalfIntegral (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Prop :=
  ∀ i j, algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele

omit [Fintype I] in
theorem halfIntegral_neg (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : HalfIntegral B) : HalfIntegral (-B) := by
  intro i j
  change algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * (-B i j) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele
  rw [mul_neg]
  exact RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.neg_mem (hB i j)

theorem quadratic_integral (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : HalfIntegral B)
    (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) : RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_entries]
  apply RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem
  intro i _
  apply RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem
  intro j _
  exact RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem (hx i) (hB i j)) (hx j)

theorem quadratic_vacuum (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : HalfIntegral B) :
    Quadratic.CM.finiteQuadratic B RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  apply Subtype.ext
  funext x
  change Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x
  by_cases hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors
  · rw [Constructed.AdelicCharacter.CM.Finite.character_integral _ (quadratic_integral B hB x hx), one_mul]
  · rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_notMem hx, mul_zero]

theorem lower_vacuum (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (hi : HalfIntegral B) :
    BareNe.CM.Group.bareAction (LowerBare.lowerLift B hB) RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  change FourierHeisenberg.CM.Equiv.fourierEquiv.symm (Quadratic.CM.finiteQuadratic (-B) (FourierHeisenberg.CM.Equiv.fourierEquiv RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction)) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction
  rw [fourier_vacuum, quadratic_vacuum (-B) (halfIntegral_neg B hi), inverse_fourier_vacuum]

theorem vacuum_ne_zero : (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) ≠ 0 := by
  intro h
  have he := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I => f.val 0) h
  change RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = 0 at he
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem] at he
  exact one_ne_zero he

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM

end

end OAI
