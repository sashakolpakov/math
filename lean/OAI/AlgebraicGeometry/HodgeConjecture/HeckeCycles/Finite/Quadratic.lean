import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator
import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator

/-! # Quadratic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM

noncomputable section

/-! Actual finite quadratic multiplier automorphisms and their
unitary Heisenberg covariance, with the constructed additive character. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.MeasureTheory
open OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM

variable {ι : Type*} [Fintype ι]

theorem finiteQuadratic_mem (B : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    (fun x => Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * f.val x) ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι := by
  obtain ⟨hf, hc⟩ := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff f.val).mp f.property
  apply (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
  refine ⟨?_, hc.mul_left⟩
  apply IsLocallyConstant.mul _ hf
  apply Constructed.AdelicCharacter.CM.Finite.character_locallyConstant.comp_continuous
  have he : RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B =
      fun x => ∑ i, ∑ j, x i * (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) * x j :=
    funext (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_entries B)
  rw [he]
  exact continuous_finsetSum Finset.univ (fun i _ =>
    continuous_finsetSum Finset.univ (fun j _ =>
      ((continuous_apply i).mul continuous_const).mul (continuous_apply j)))

def finiteQuadratic (B : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι where
  toFun f := ⟨fun x => Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * f.val x,
    finiteQuadratic_mem B f⟩
  invFun f := ⟨fun x => Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (-B) x) * f.val x,
    finiteQuadratic_mem (-B) f⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (-B) x) *
      (Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * f.val x) = f.val x
    rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_neg, ← mul_assoc, ← Constructed.AdelicCharacter.CM.Finite.character.map_add_eq_mul]
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    change Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) *
      (Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (-B) x) * f.val x) = f.val x
    rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_neg, ← mul_assoc, ← Constructed.AdelicCharacter.CM.Finite.character.map_add_eq_mul]
    simp
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact mul_left_comm _ _ _

theorem finiteQuadratic_apply (B : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (finiteQuadratic B f).val x = Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * f.val x := rfl

theorem finiteQuadratic_intertwines (B : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)
      (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB) (finiteQuadratic B) := by
  intro p q f h hh x
  rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper_phase]
  change Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * h.val x =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character (p + B *ᵥ q) q
      (fun y => Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B y) * f.val y) x
  rw [hh]
  exact RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_heisenberg Constructed.AdelicCharacter.CM.Finite.character B hB p q x f.val

theorem unitary (B : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    FiniteOscillator.CM.integralPairing (finiteQuadratic B f) (finiteQuadratic B h) = FiniteOscillator.CM.integralPairing f h := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * f.val x) *
      star (Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * h.val x) = _
    let z := Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x)
    have hz : z * star z = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Constructed.AdelicCharacter.CM.Finite.character_unitary]
      norm_num
    rw [star_mul]
    calc
      _ = (z * star z) * (f.val x * star (h.val x)) := by ring
      _ = _ := by rw [hz, one_mul]

def quadraticOscillator (B : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) : FiniteOscillator.CM.Oscillator (I := ι) :=
  ⟨(RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB, finiteQuadratic B), unitary B,
    FiniteOscillator.CM.graph_of_intertwines _ _ (finiteQuadratic_intertwines B hB)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM
