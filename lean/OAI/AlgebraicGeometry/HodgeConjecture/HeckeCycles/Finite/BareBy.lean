import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixElimination
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticFactorization

/-! # Bare By -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareBy.CM.UnipotentGeneration

/-! Upper and lower unipotents generate the actual finite adelic
symplectic group. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM
variable {I : Type*} [Fintype I]

def leviHom : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf where
  toFun := RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi
  map_one' := by
    apply Subtype.ext
    simp [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi]
  map_mul' A B := by
    apply Subtype.ext
    change (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi (A * B)).val = (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A).val * (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi B).val
    simp [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi, _root_.mul_inv_rev, Matrix.transpose_mul, Matrix.fromBlocks_multiply]

theorem weyl_factorization :
    FourierHeisenberg.CM.weyl (I := I) = RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-1) Matrix.isSymm_one.neg *
      IntegralVacuum.CM.LowerBare.lower 1 Matrix.isSymm_one * RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-1) Matrix.isSymm_one.neg := by
  apply Subtype.ext
  change (FourierHeisenberg.CM.weyl (I := I)).val =
    (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-1) Matrix.isSymm_one.neg).val *
      (IntegralVacuum.CM.LowerBare.lower 1 Matrix.isSymm_one).val * (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-1) Matrix.isSymm_one.neg).val
  simp [FourierHeisenberg.CM.weyl, RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper, IntegralVacuum.CM.LowerBare.lower, Matrix.fromBlocks_multiply]

theorem symmetric_levi_factorization (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (hA : A.val.IsSymm) :
    ∃ (hAi : (A⁻¹).val.IsSymm), RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A * FourierHeisenberg.CM.weyl =
      RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-A.val) hA.neg * IntegralVacuum.CM.LowerBare.lower (A⁻¹).val hAi * RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-A.val) hA.neg := by
  have hi : (A⁻¹).val.IsSymm := by simpa only [Matrix.coe_units_inv] using hA.inv
  refine ⟨hi, ?_⟩
  apply Subtype.ext
  change (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A).val * FourierHeisenberg.CM.weyl.val =
    (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-A.val) hA.neg).val * (IntegralVacuum.CM.LowerBare.lower (A⁻¹).val hi).val *
      (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-A.val) hA.neg).val
  simp [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi, FourierHeisenberg.CM.weyl, RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper, IntegralVacuum.CM.LowerBare.lower, Matrix.fromBlocks_multiply, hA.inv.eq]

theorem generated_by_unipotents (H : Subgroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))
    (hU : ∀ (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm), RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB ∈ H)
    (hL : ∀ (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm), IntegralVacuum.CM.LowerBare.lower B hB ∈ H) : H = ⊤ := by
  have hW : FourierHeisenberg.CM.weyl (I := I) ∈ H := by
    rw [weyl_factorization]
    exact H.mul_mem (H.mul_mem (hU _ _) (hL _ _)) (hU _ _)
  have hSym (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (hA : A.val.IsSymm) : RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A ∈ H := by
    obtain ⟨hi, hfactor⟩ := symmetric_levi_factorization A hA
    have h : RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A * FourierHeisenberg.CM.weyl ∈ H := by
      rw [hfactor]
      exact H.mul_mem (H.mul_mem (hU _ _) (hL _ hi)) (hU _ _)
    have hh := H.mul_mem h (H.inv_mem hW)
    simpa only [mul_inv_cancel_right] using hh
  have hGL : H.comap leviHom = ⊤ :=
    MatrixElimination.CM.SymmetricGeneration.generated_by_symmetric _ hSym
  have hLevi (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) : RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A ∈ H := by
    have h : A ∈ H.comap leviHom := by rw [hGL]; trivial
    exact h
  apply top_unique
  intro g _
  obtain ⟨X, hX, A, C, hC, D, hD, hg⟩ := SymplecticFactorization.CM.exists_factorization g
  rw [hg]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hU _ _) (hL C hC)) (hLevi A)) (hU D hD)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareBy.CM.UnipotentGeneration

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareBy.CM.Surjective

/-! Surjectivity of the intrinsic finite bare group. Every actual
finite adelic symplectic matrix has a bare lift. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.QuadraticBare.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare
variable {I : Type*} [Fintype I]

theorem projection_surjective : Function.Surjective (BareNe.CM.Group.bareProjection (I := I)) := by
  apply MonoidHom.range_eq_top.mp
  apply UnipotentGeneration.generated_by_unipotents
  · intro B hB
    exact MonoidHom.mem_range.mpr ⟨QuadraticBare.CM.quadraticLift B hB, QuadraticBare.CM.quadraticLift_projection B hB⟩
  · intro B hB
    exact MonoidHom.mem_range.mpr ⟨IntegralVacuum.CM.LowerBare.lowerLift B hB, IntegralVacuum.CM.LowerBare.lowerLift_projection B hB⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareBy.CM.Surjective

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareBy.CM.Generators

/-! Every bare operator is generated by the explicitly constructed
upper and lower quadratic operators and the negative identity. -/

open scoped Classical commutatorElement
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.QuadraticBare.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare
variable {I : Type*} [Fintype I]

section Group
variable {G : Type*} [Group G]

theorem central_mul_commutator (z a b : G) (hz : ∀ g, Commute z g) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, (hz b).commutator_eq, mul_one,
    (hz ⁅a, b⁆).eq, mul_inv_cancel_right]

theorem commutator_central_mul (a z b : G) (hz : ∀ g, Commute z g) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, (hz a).symm.commutator_eq, one_mul,
    (hz ⁅a, b⁆).eq, mul_inv_cancel_right]
end Group

def generatorSet : Set (FiniteOscillator.CM.Oscillator (I := I)) :=
  {g | g = BareNe.CM.Group.minus ∨
    (∃ (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm), g = Quadratic.CM.quadraticOscillator B hB) ∨
    (∃ (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm), g = (IntegralVacuum.CM.LowerBare.lowerLift B hB).val)}

def generated : Subgroup (FiniteOscillator.CM.Oscillator (I := I)) := Subgroup.closure generatorSet

theorem upper_mem (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    Quadratic.CM.quadraticOscillator B hB ∈ generated :=
  Subgroup.subset_closure (Or.inr (Or.inl ⟨B, hB, rfl⟩))

theorem lower_mem (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    (IntegralVacuum.CM.LowerBare.lowerLift B hB).val ∈ generated :=
  Subgroup.subset_closure (Or.inr (Or.inr ⟨B, hB, rfl⟩))

theorem minus_mem : BareNe.CM.Group.minus (I := I) ∈ generated := Subgroup.subset_closure (Or.inl rfl)

theorem generated_le_bare : generated (I := I) ≤ BareNe.CM.Group.bareSubgroup := by
  rw [generated, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩
  · exact Subgroup.subset_closure (Or.inr rfl)
  · exact QuadraticBare.CM.quadratic_mem B hB
  · exact (IntegralVacuum.CM.LowerBare.lowerLift B hB).property

def generatedProjection : generated (I := I) →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  FiniteOscillator.CM.projection.comp generated.subtype

theorem generatedProjection_surjective : Function.Surjective (generatedProjection (I := I)) := by
  apply MonoidHom.range_eq_top.mp
  apply UnipotentGeneration.generated_by_unipotents
  · intro B hB
    exact MonoidHom.mem_range.mpr ⟨⟨Quadratic.CM.quadraticOscillator B hB, upper_mem B hB⟩, rfl⟩
  · intro B hB
    exact MonoidHom.mem_range.mpr ⟨⟨(IntegralVacuum.CM.LowerBare.lowerLift B hB).val, lower_mem B hB⟩,
      IntegralVacuum.CM.LowerBare.lowerLift_projection B hB⟩

theorem central_times_generated (g : FiniteOscillator.CM.Oscillator (I := I)) :
    ∃ (z a : FiniteOscillator.CM.Oscillator (I := I)), (∀ h, Commute z h) ∧ a ∈ generated ∧ g = z * a := by
  obtain ⟨a, ha⟩ := generatedProjection_surjective (FiniteOscillator.CM.projection g)
  have hz : FiniteOscillator.CM.projection (g * a.val⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change FiniteOscillator.CM.projection g * (generatedProjection a)⁻¹ = 1
    rw [ha, mul_inv_cancel]
  exact ⟨g * a.val⁻¹, a.val, BareNe.CM.OscillatorKernel.kernel_central _ hz,
    a.property, (inv_mul_cancel_right g a.val).symm⟩

theorem commutator_mem (g h : FiniteOscillator.CM.Oscillator (I := I)) : ⁅g, h⁆ ∈ generated := by
  obtain ⟨z, a, hz, ha, rfl⟩ := central_times_generated g
  obtain ⟨w, b, hw, hb, rfl⟩ := central_times_generated h
  rw [central_mul_commutator z a _ hz, commutator_central_mul a w b hw]
  exact generated.mul_mem (generated.mul_mem (generated.mul_mem ha hb)
    (generated.inv_mem ha)) (generated.inv_mem hb)

theorem bare_eq_generated : BareNe.CM.Group.bareSubgroup (I := I) = generated := by
  apply le_antisymm _ generated_le_bare
  change Subgroup.closure _ ≤ generated
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with ⟨a, b, rfl⟩ | rfl
  · exact commutator_mem a b
  · exact minus_mem

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareBy.CM.Generators

end

end OAI
