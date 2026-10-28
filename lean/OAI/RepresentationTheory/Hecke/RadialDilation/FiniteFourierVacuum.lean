import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteGenerators
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteOrderPhase
import OAI.RepresentationTheory.Hecke.RadialDilation.RingWeyl
import OAI.RepresentationTheory.Theta.AdelicTopology

/-! # Finite Fourier Vacuum -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteFourierVacuum.Realization

noncomputable section

/-! PoissonAutomorphy's finite Fourier action and its eighth-root phase on the integral lattice vector. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.MeasureTheory OAI.RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finiteInput_real_vacuum_fourier_zero (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) :
    Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume D.vacuum.val 0 = 1 := by
  have hscalar : (∫ t : ℝ, Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2))) = 1 := by
    have h := integral_gaussian_complex (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos)
    simpa only [neg_mul, div_self (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
      Complex.one_cpow] using h
  have heq : D.vacuum.val = fun x : ι → ℝ =>
      ∏ i, Complex.exp (-((Real.pi : ℂ) * (x i : ℂ) ^ 2)) := by
    funext x
    rw [D.vacuum_eq, ← Complex.exp_sum]
    congr 1
    simp only [Finset.sum_neg_distrib, Finset.mul_sum]
  simp only [Theta.PoissonAutomorphyNormalizationData.fourier, Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero,
    AddChar.map_zero_eq_one, mul_one]
  rw [heq]
  calc
    _ = ∏ _i : ι, ∫ t : ℝ, Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2)) := by
      convert! integral_fintype_prod_volume_eq_prod
        (fun _i : ι => fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2))) using 1
    _ = _ := by simp only [hscalar, Finset.prod_const_one]

theorem finiteAction_rational_fourier (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (hγ : γ.val = Matrix.fromBlocks 0 (-1) 1 0)
    (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finiteAction γ φ).val x = Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (Theta.PoissonAutomorphyNormalizationData.toSiegel (Theta.PoissonAutomorphyNormalizationData.basePeriod ι)) *
      Theta.PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure φ.val x := by
  rw [FiniteGenerators.Realization.finiteAction_from_rational_at_zero]
  change _ * (D.adelic.action (D.rationalSplit γ) (Theta.PoissonAutomorphyNormalizationData.tensor D.vacuum φ)).val (FiniteGenerators.Realization.adelicAtFinite x) = _
  rw [D.rational_fourier γ hγ]
  change _ * Theta.PoissonAutomorphyNormalizationData.fourier D.character (Theta.PoissonAutomorphyNormalizationData.adelicMeasure D.finiteMeasure)
    (Theta.PoissonAutomorphyNormalizationData.pureTensor D.vacuum φ) (FiniteGenerators.Realization.adelicAtFinite x) = _
  rw [Theta.AdelicTopology.PoissonAutomorphyConstruction.adelic_fourier_pureTensor]
  change _ * (Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume D.vacuum.val 0 *
    Theta.PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure φ.val x) = _
  rw [finiteInput_real_vacuum_fourier_zero, one_mul]

theorem finiteAction_weyl_vacuum (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) :
    D.finiteAction (RingWeyl.Realization.ringWeyl ℚ) Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction =
      Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks (RingWeyl.Realization.ringWeyl ℚ)) (Theta.PoissonAutomorphyNormalizationData.toSiegel (Theta.PoissonAutomorphyNormalizationData.basePeriod ι)) • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  apply Subtype.ext
  funext x
  rw [finiteAction_rational_fourier D (RingWeyl.Realization.ringWeyl ℚ) rfl]
  change _ * Theta.PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x =
    _ * Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x
  rw [Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_selfFourier]

omit [DecidableEq ι] in
theorem finite_integral_vacuum_ne_zero : (Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) ≠ 0 := by
  intro h
  have he := congrArg (fun f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι => f.val 0) h
  change Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : ι → Theta.PoissonAutomorphyNormalizationData.AQf) = 0 at he
  rw [Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem] at he
  exact one_ne_zero he

theorem every_finite_weyl_vacuum_phase (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (m : MpF) (hm : D.finite.project m = Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) (RingWeyl.Realization.ringWeyl ℚ)) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ D.finite.action m Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = ξ • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
  obtain ⟨ε, _, hε⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D m (D.finiteLift (RingWeyl.Realization.ringWeyl ℚ))
    (hm.trans (D.finiteLift_covers _).symm)
  let ξ := ε * Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks (RingWeyl.Realization.ringWeyl ℚ)) (Theta.PoissonAutomorphyNormalizationData.toSiegel (Theta.PoissonAutomorphyNormalizationData.basePeriod ι))
  have hfix : D.finite.action m Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = ξ • Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction := by
    rw [hε]
    change ε • D.finiteAction (RingWeyl.Realization.ringWeyl ℚ) Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = _
    rw [finiteAction_weyl_vacuum, smul_smul]
  refine ⟨ξ, ?_, hfix⟩
  have hp : D.finite.project m ^ 4 = 1 := by
    rw [hm, ← map_pow, RingWeyl.Realization.ringWeyl_fourth, map_one]
  exact FiniteOrderPhase.Realization.finite_cover_eigenphase_order D m 4 hp Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction
    finite_integral_vacuum_ne_zero ξ hfix

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteFourierVacuum.Realization
