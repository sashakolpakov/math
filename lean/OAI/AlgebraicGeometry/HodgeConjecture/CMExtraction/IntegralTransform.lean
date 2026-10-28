import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnipotentIntegrable
import OAI.RepresentationTheory.Hecke.Satake

/-! # Integral Transform -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralTransform.Iwasawa

noncomputable section

section

/-! Match the actual inverse-representative raw Hecke kernel with CosetCalculus's
positive matrix double-coset indicator, without changing either convention. -/

open scoped Classical TensorProduct

variable (q : ℕ) [Fact q.Prime]

theorem gl3Torus_matrix (a : Fin 3 → ℤ) :
    (HeightFibers.Iwasawa.gl3Torus q a).val = Matrix.diagonal
      (fun i => (algebraMap ℤ_[q] ℚ_[q] (q : ℤ_[q])) ^ a i) := by
  ext i j
  simp [HeightFibers.Iwasawa.gl3Torus, AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, AbelianScheme.TateComparison.HeckeKernel.qUnit]

theorem gl3_positive_doubleCoset_iff (a : Fin 3 → ℤ) (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
    (∃ k l : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q, g = k.val * HeightFibers.Iwasawa.gl3Torus q a * l.val) ↔
      RepresentationTheory.Hecke.DoubleCoset.Calculus.InDoubleCoset (q : ℤ_[q]) a g.val := by
  constructor
  · rintro ⟨k, l, hg⟩
    obtain ⟨U, hU⟩ := k.property
    obtain ⟨V, hV⟩ := l.property
    refine ⟨U, V, ?_⟩
    have h := congrArg Units.val hg
    rw [Units.val_mul, Units.val_mul, gl3Torus_matrix, ← hU, ← hV] at h
    exact h
  · rintro ⟨U, V, h⟩
    refine ⟨⟨Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) U, ⟨U, rfl⟩⟩,
      ⟨Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) V, ⟨V, rfl⟩⟩, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, gl3Torus_matrix]
    exact h

def positiveGL3Hecke (a : Fin 3 → ℤ) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :=
  Operators.Local.rawGL3Hecke q (HeightFibers.Iwasawa.gl3Torus q a)⁻¹

theorem positiveGL3Hecke_kernel (a : Fin 3 → ℤ) (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
    AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (positiveGL3Hecke q a) (QuotientGroup.mk g) =
      if RepresentationTheory.Hecke.DoubleCoset.Calculus.InDoubleCoset (q : ℤ_[q]) a g.val then 1 else 0 := by
  rw [positiveGL3Hecke, Operators.Local.rawGL3Hecke_isRaw q (HeightFibers.Iwasawa.gl3Torus q a)⁻¹ g, inv_inv,
    gl3_positive_doubleCoset_iff]

theorem positiveGL3Hecke_complex_kernel (a : Fin 3 → ℤ) (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
    RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)
        (HeckeScalarExtension.Iwasawa.rationalComplexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (positiveGL3Hecke q a)) (QuotientGroup.mk g) =
      RepresentationTheory.Hecke.Satake.CosetCalculus.rawDoubleCoset (q : ℤ_[q]) a g.val := by
  rw [HeckeScalarExtension.Iwasawa.rationalComplexHecke_kernel]
  change (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (positiveGL3Hecke q a)
    (QuotientGroup.mk g) : ℂ) = _
  rw [positiveGL3Hecke_kernel]
  split_ifs with h <;> simp [RepresentationTheory.Hecke.Satake.CosetCalculus.rawDoubleCoset, h]

variable [MeasurableSpace ℚ_[q]] [BorelSpace ℚ_[q]]
  (μ : MeasureTheory.Measure ℚ_[q]) [μ.IsAddLeftInvariant]
  (hO : MeasurableSet (Unipotent.Iwasawa.padicIntegralSet q)) (hvol : μ (Unipotent.Iwasawa.padicIntegralSet q) = 1)

include hO hvol in
theorem positiveGL3Hecke_constantTerm (a ell : Fin 3 → ℤ) :
    ((Iwasawa.gl3Decomposition q).constantTerm
      (HeckeScalarExtension.Iwasawa.rationalComplexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (positiveGL3Hecke q a))).coeff ell =
        ∫ x, ∫ z, ∫ y, RepresentationTheory.Hecke.Satake.CosetCalculus.rawDoubleCoset (q : ℤ_[q]) a
          (RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure.triangular (q : ℚ_[q]) ell x y z) ∂μ ∂μ ∂μ := by
  rw [UnipotentIntegrable.Iwasawa.gl3_constantTerm_unipotent q μ hO hvol]
  unfold UnipotentIntegrable.Iwasawa.gl3UnipotentKernelIntegral
  simp_rw [positiveGL3Hecke_complex_kernel]
  simp only [HeightFibers.Iwasawa.gl3Torus, Unipotent.Iwasawa.gl3Torus_mul_unipotent]

end

/-! The actual normalized finite-support GL3 transform evaluates to
CosetCalculus's normalized integral transform on the same positive raw indicator. -/

open scoped Classical TensorProduct BigOperators
open _root_.MeasureTheory

theorem evaluateTorus_as_tsum (t : Fin 3 → ℂˣ) (P : AddMonoidAlgebra ℂ (Fin 3 → ℤ)) :
    SatakeKernel.Iwasawa.evaluateLattice ((Units.coeHom ℂ).comp (SatakeParameters.Iwasawa.torusCharacter t)) P =
      ∑' ell : Fin 3 → ℤ, P.coeff ell * RepresentationTheory.Hecke.Satake.CosetCalculus.torusMonomial t ell := by
  unfold SatakeKernel.Iwasawa.evaluateLattice
  rw [AddMonoidAlgebra.lift_apply']
  rw [tsum_eq_sum (s := P.coeff.support) (fun ell hell => by
    have hz : P.coeff ell = 0 := Finsupp.notMem_support_iff.mp hell
    rw [hz, zero_mul])]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro ell _
  change P.coeff ell * (SatakeParameters.Iwasawa.torusCharacter t (Multiplicative.ofAdd ell) : ℂ) = _
  simp [SatakeParameters.Iwasawa.torusCharacter, RepresentationTheory.Hecke.Satake.CosetCalculus.torusMonomial, Fin.prod_univ_three]

variable (q : ℕ) [Fact q.Prime]

theorem gl3NormalizedSatake_constant_coeff (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))
    (ell : Fin 3 → ℤ) :
    (Satake.Iwasawa.gl3NormalizedSatake q (1 ⊗ₜ[ℚ] T)).coeff ell =
      ((Iwasawa.gl3Decomposition q).constantTerm (HeckeScalarExtension.Iwasawa.rationalComplexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T)).coeff ell *
        (q : ℂ) ^ (ell 2 - ell 0) := by
  unfold Satake.Iwasawa.gl3NormalizedSatake
  rw [AlgHom.comp_apply, HeckeScalarExtension.Iwasawa.complexHecke_tmul, one_smul, RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.satake_coeff]
  congr 1
  have hs : (Real.sqrt (q : ℝ) : ℂ) ^ (2 : ℤ) = (q : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  rw [← hs, ← zpow_mul]
  congr 1
  simp [RepresentationTheory.Satake.GL3GL.Core.twoRho]
  ring

theorem gl3RationalSatake_scalar_extension (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    AddMonoidAlgebra.mapRingHom (Fin 3 → ℤ) (algebraMap ℚ ℂ) (Satake.Iwasawa.gl3RationalSatake q T) =
      Satake.Iwasawa.gl3NormalizedSatake q (1 ⊗ₜ[ℚ] T) := by
  ext ell
  exact Satake.Iwasawa.gl3RationalSatakeCoefficients_cast q T ell

theorem gl3TorusSatakeOver_complex (t : Fin 3 → ℂˣ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t T =
      SatakeKernel.Iwasawa.evaluateLattice ((Units.coeHom ℂ).comp (SatakeParameters.Iwasawa.torusCharacter t))
        (Satake.Iwasawa.gl3NormalizedSatake q (1 ⊗ₜ[ℚ] T)) := by
  unfold TorusCharacters.Iwasawa.gl3TorusSatakeOver
  rw [AlgHom.comp_apply, SatakeBaseChange.Iwasawa.rationalLatticeEvaluation_complex, gl3RationalSatake_scalar_extension]

variable [MeasurableSpace ℚ_[q]] [BorelSpace ℚ_[q]]
  (μ : Measure ℚ_[q]) [μ.IsAddLeftInvariant]
  (hO : MeasurableSet (Unipotent.Iwasawa.padicIntegralSet q)) (hvol : μ (Unipotent.Iwasawa.padicIntegralSet q) = 1)

include hO hvol in
theorem gl3TorusSatakeOver_positive_integral (a : Fin 3 → ℤ) (t : Fin 3 → ℂˣ) :
    TorusCharacters.Iwasawa.gl3TorusSatakeOver q t (positiveGL3Hecke q a) =
      RepresentationTheory.Hecke.Satake.CosetCalculus.normalizedSatake q (q : ℤ_[q]) μ (RepresentationTheory.Hecke.Satake.CosetCalculus.rawDoubleCoset (q : ℤ_[q]) a) t := by
  rw [gl3TorusSatakeOver_complex, evaluateTorus_as_tsum]
  unfold RepresentationTheory.Hecke.Satake.CosetCalculus.normalizedSatake
  apply tsum_congr
  intro ell
  rw [gl3NormalizedSatake_constant_coeff, positiveGL3Hecke_constantTerm q μ hO hvol]
  rw [map_natCast]
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralTransform.Iwasawa
