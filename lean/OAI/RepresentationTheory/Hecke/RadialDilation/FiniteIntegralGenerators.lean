import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteIntegralQuadratic
import OAI.RepresentationTheory.Hecke.RadialDilation.EighthPhaseSubgroup

/-! # Finite Integral Generators -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteIntegralGenerators.Realization

noncomputable section

/-! A concrete integral generator subgroup has eighth-root phases on the finite lattice vector. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteIntegralGeneratorSet : Set (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) :=
  {g | g = RingWeyl.Realization.ringWeyl Theta.PoissonAutomorphyNormalizationData.AQf ∨ ∃ (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm),
    FiniteIntegralQuadratic.Realization.HalfIntegralMatrix B ∧ g = QuadraticCommutator.Realization.ringUpper B hB}

def finiteIntegralGeneratorSubgroup : Subgroup (Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) :=
  Subgroup.closure finiteIntegralGeneratorSet

theorem finiteIntegralGeneratorSubgroup_upper (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf)
    (hB : B.IsSymm) (hBi : FiniteIntegralQuadratic.Realization.HalfIntegralMatrix B) :
    QuadraticCommutator.Realization.ringUpper B hB ∈ finiteIntegralGeneratorSubgroup :=
  Subgroup.subset_closure (Or.inr ⟨B, hB, hBi, rfl⟩)

theorem finiteIntegralGeneratorSubgroup_weyl :
    RingWeyl.Realization.ringWeyl Theta.PoissonAutomorphyNormalizationData.AQf (ι := ι) ∈ finiteIntegralGeneratorSubgroup :=
  Subgroup.subset_closure (Or.inl rfl)

theorem finiteIntegralGeneratorSubgroup_lower (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf)
    (hB : B.IsSymm) (hBi : FiniteIntegralQuadratic.Realization.HalfIntegralMatrix B) :
    RingWeyl.Realization.ringLower Theta.PoissonAutomorphyNormalizationData.AQf B hB ∈ finiteIntegralGeneratorSubgroup := by
  rw [RingWeyl.Realization.ringLower_conjugation]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ finiteIntegralGeneratorSubgroup_weyl
      (finiteIntegralGeneratorSubgroup_upper (-B) hB.neg hBi.neg))
    (Subgroup.inv_mem _ finiteIntegralGeneratorSubgroup_weyl)

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finite_integral_generators_phase_image (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) :
    finiteIntegralGeneratorSubgroup ≤
      (EighthPhaseSubgroup.Realization.eighthPhaseStabilizer D.finite.action Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).map D.finite.project := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | ⟨B, hB, hBi, rfl⟩
  · refine ⟨D.finiteLift (RingWeyl.Realization.ringWeyl ℚ), ?_, ?_⟩
    · exact FiniteFourierVacuum.Realization.every_finite_weyl_vacuum_phase D _ (D.finiteLift_covers _)
    · rw [D.finiteLift_covers, RingWeyl.Realization.map_ringWeyl]
  · obtain ⟨m, hm, ha⟩ := FiniteQuadraticLift.Realization.exists_finite_quadratic_lift D B hB
    refine ⟨m, ?_, hm⟩
    refine ⟨1, by norm_num, ?_⟩
    rw [ha, FiniteIntegralQuadratic.Realization.finiteQuadratic_integral_vacuum D B hBi, one_smul]

theorem every_finite_integral_generator_phase (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (m : MpF) (hm : D.finite.project m ∈ finiteIntegralGeneratorSubgroup) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ D.finite.action m Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = ξ • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  obtain ⟨u, hu, hup⟩ := finite_integral_generators_phase_image D hm
  obtain ⟨ζ, hζ, huf⟩ := hu
  obtain ⟨ε, hε, hma⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D m u hup.symm
  have hε8 : ε ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
  refine ⟨ε * ζ, by rw [mul_pow, hε8, hζ, mul_one], ?_⟩
  rw [hma, huf, smul_smul]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteIntegralGenerators.Realization
