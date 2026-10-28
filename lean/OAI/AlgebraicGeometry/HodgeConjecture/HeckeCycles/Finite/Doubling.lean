import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Dilation
import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator

/-! # Doubling -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Doubling.CM

noncomputable section

/-! The actual normalized doubling operator covers the rational
symplectic dilation in the finite oscillator group. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Dilation.CM

variable {I : Type*} [Fintype I]

def doubling : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I := Dilation.CM.dilation 2 (by norm_num)

theorem doubling_apply (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (doubling f).val x =
      (ScaleMeasure.CM.normalizingScalar (I := I) 2 (by norm_num) : ℂ) * f.val ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • x) := by
  rw [doubling, Dilation.CM.dilation_apply]
  congr 2
  apply congrArg f.val
  funext i
  change algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf 2 * x i = (2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) * x i
  rw [map_ofNat]

def symplectic : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.rationalDoubleSymplectic

theorem symplectic_phase (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (symplectic (I := I)).val *ᵥ Sum.elim p q =
      Sum.elim ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • p) (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • q) := by
  rw [symplectic, RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.rationalDoubleSymplectic_map]
  funext i
  cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.one_apply, Matrix.smul_apply]

theorem heisenberg_doubling (p q x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) (c : ℂ) :
    c * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q f ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • p)
        (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • q) (fun y => c * f ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • y)) x := by
  have hh : (2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) * algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) = 1 := FourierHeisenberg.CM.half_two
  have hp : (∑ i, p i * (((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • x) i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) =
      ∑ i, ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • p) i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) *
        (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • q) i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (p i * algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i) * hh
  have hx : (fun i => ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • x) i - q i) =
      (2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • (fun i => x i - (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) • q) i) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (q i) * hh
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg
  rw [hp, hx]
  ring

theorem intertwines : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) symplectic doubling := by
  intro p q f h hh x
  rw [doubling_apply, hh, symplectic_phase]
  have he := heisenberg_doubling p q x f.val
    (ScaleMeasure.CM.normalizingScalar (I := I) 2 (by norm_num) : ℂ)
  rw [he]
  rw [show (doubling f).val =
    (fun y => (ScaleMeasure.CM.normalizingScalar (I := I) 2 (by norm_num) : ℂ) * f.val ((2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) • y))
    from funext (doubling_apply f)]
  rfl

def doublingOscillator : FiniteOscillator.CM.Oscillator (I := I) :=
  ⟨(symplectic, doubling), Dilation.CM.unitary 2 (by norm_num),
    FiniteOscillator.CM.graph_of_intertwines _ _ intertwines⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Doubling.CM
