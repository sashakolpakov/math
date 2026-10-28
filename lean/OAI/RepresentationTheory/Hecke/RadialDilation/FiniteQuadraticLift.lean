import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadratic
import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteGenerators
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur

/-! # Finite Quadratic Lift -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadraticLift.Realization

noncomputable section

/-! Every finite-adelic quadratic multiplier is exactly an operator in PoissonAutomorphy's cover. -/

open scoped Classical _root_.Matrix commutatorElement
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rationalDouble_substitution {K : Type*} [CommRing K] [Algebra ℚ K]
    (x : ι → K) :
    (QuadraticCommutator.Realization.rationalDoubleMatrix (ι := ι)).val.transpose.map (algebraMap ℚ K) *ᵥ x =
      (2 : K) • x := by
  have hm := congrArg Matrix.toBlocks₁₁ (QuadraticCommutator.Realization.rationalDoubleSymplectic_map (ι := ι) (K := K))
  change ((2 : ℚ) • (1 : Matrix ι ι ℚ)).map (algebraMap ℚ K) = (2 : K) • 1 at hm
  change (((2 : ℚ) • (1 : Matrix ι ι ℚ)).transpose.map (algebraMap ℚ K)) *ᵥ x = _
  rw [Matrix.transpose_smul, Matrix.transpose_one, hm, Matrix.smul_mulVec, Matrix.one_mulVec]

omit [DecidableEq ι] in
theorem ringQuadratic_doubling {K : Type*} [CommRing K] [Algebra ℚ K]
    (B : Matrix ι ι K) (x : ι → K) :
    QuadraticCommutator.Realization.ringQuadratic (algebraMap ℚ K (1 / 3) • B) ((2 : K) • x) =
      QuadraticCommutator.Realization.ringQuadratic B x + QuadraticCommutator.Realization.ringQuadratic (algebraMap ℚ K (1 / 3) • B) x := by
  rw [QuadraticCommutator.Realization.ringQuadratic_smul_vector, QuadraticCommutator.Realization.ringQuadratic_smul_matrix]
  have hc : (2 : K) ^ 2 * algebraMap ℚ K (1 / 3) = 1 + algebraMap ℚ K (1 / 3) := by
    have h := congrArg (algebraMap ℚ K)
      (show (2 : ℚ) ^ 2 * (1 / 3) = 1 + 1 / 3 by norm_num)
    simpa only [map_mul, map_pow, map_add, map_one, map_ofNat] using h
  rw [← mul_assoc, hc, add_mul, one_mul]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finiteAction_double_apply (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finiteAction QuadraticCommutator.Realization.rationalDoubleSymplectic f).val x =
      Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks QuadraticCommutator.Realization.rationalDoubleSymplectic) (Theta.PoissonAutomorphyNormalizationData.toSiegel (Theta.PoissonAutomorphyNormalizationData.basePeriod ι)) *
        f.val ((2 : Theta.PoissonAutomorphyNormalizationData.AQf) • x) := by
  rw [FiniteGenerators.Realization.finiteAction_rational_linear D QuadraticCommutator.Realization.rationalDoubleSymplectic QuadraticCommutator.Realization.rationalDoubleMatrix rfl,
    rationalDouble_substitution]

theorem finiteQuadratic_commutator (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) :
    ⁅D.finiteAction QuadraticCommutator.Realization.rationalDoubleSymplectic,
      FiniteQuadratic.Realization.finiteQuadratic D (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B)⁆ = FiniteQuadratic.Realization.finiteQuadratic D B := by
  have hrel : D.finiteAction QuadraticCommutator.Realization.rationalDoubleSymplectic *
      FiniteQuadratic.Realization.finiteQuadratic D (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) =
      FiniteQuadratic.Realization.finiteQuadratic D B * FiniteQuadratic.Realization.finiteQuadratic D (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) *
        D.finiteAction QuadraticCommutator.Realization.rationalDoubleSymplectic := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    change (D.finiteAction QuadraticCommutator.Realization.rationalDoubleSymplectic
      (FiniteQuadratic.Realization.finiteQuadratic D (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) f)).val x =
      (FiniteQuadratic.Realization.finiteQuadratic D B (FiniteQuadratic.Realization.finiteQuadratic D (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B)
        (D.finiteAction QuadraticCommutator.Realization.rationalDoubleSymplectic f))).val x
    rw [finiteAction_double_apply, FiniteQuadratic.Realization.finiteQuadratic_apply, FiniteQuadratic.Realization.finiteQuadratic_apply,
      FiniteQuadratic.Realization.finiteQuadratic_apply, finiteAction_double_apply, ringQuadratic_doubling,
      D.finiteCharacter.map_add_eq_mul]
    ring
  rw [commutatorElement_def, hrel]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem exists_finite_quadratic_lift (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    ∃ m : MpF, D.finite.project m = QuadraticCommutator.Realization.ringUpper B hB ∧
      D.finite.action m = FiniteQuadratic.Realization.finiteQuadratic D B := by
  have hU := D.finite.intertwines (D.finiteLift QuadraticCommutator.Realization.rationalDoubleSymplectic)
  rw [D.finiteLift_covers] at hU
  obtain ⟨m, hm, ha⟩ := FiniteSchur.Realization.finite_commutator_lift D
    (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) QuadraticCommutator.Realization.rationalDoubleSymplectic)
    (QuadraticCommutator.Realization.ringUpper (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B) (hB.smul _))
    (D.finiteAction QuadraticCommutator.Realization.rationalDoubleSymplectic)
    (FiniteQuadratic.Realization.finiteQuadratic D (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 3) • B)) hU
    (FiniteQuadratic.Realization.finiteQuadratic_intertwines D _ (hB.smul _))
  refine ⟨m, ?_, ?_⟩
  · exact hm.trans (QuadraticCommutator.Realization.rationalDouble_upper_commutator B hB)
  · exact ha.trans (finiteQuadratic_commutator D B)

theorem every_finite_quadratic_lift (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (m : MpF)
    (hm : D.finite.project m = QuadraticCommutator.Realization.ringUpper B hB) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι,
      D.finite.action m f = ε • FiniteQuadratic.Realization.finiteQuadratic D B f := by
  obtain ⟨u, hu, hua⟩ := exists_finite_quadratic_lift D B hB
  obtain ⟨ε, hε, hf⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D m u (hm.trans hu.symm)
  exact ⟨ε, hε, fun f => by rw [hf, hua]⟩

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadraticLift.Realization
