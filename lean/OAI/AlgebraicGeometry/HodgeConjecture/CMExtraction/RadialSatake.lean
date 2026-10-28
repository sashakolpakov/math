import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.ConstantTerm
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeKernel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters

/-! # Radial Satake -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake.Iwasawa

noncomputable section

section

/-! Identify the actual radial spherical character with evaluation of
the actual normalized Satake transform at (e, sqrt(q), sqrt(q) inverse). -/

open scoped Classical TensorProduct

variable (q : ℕ) [Fact q.Prime]

def normalizedSatake : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ]
    AddMonoidAlgebra ℂ (Fin 3 → ℤ) :=
  (RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.satake (Borel.Iwasawa.decomposition q) q (Fact.out : q.Prime).pos RepresentationTheory.Satake.GL3GL.Core.twoRho).comp
    (HeckeScalarExtension.Iwasawa.complexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q))

def radialSatakeCharacter (e : ℂˣ) : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ :=
  (SatakeKernel.Iwasawa.evaluateLattice ((Units.coeHom ℂ).comp (SatakeParameters.Iwasawa.torusCharacter (SatakeParameters.Iwasawa.radialTorusPoint q e)))).comp
    (normalizedSatake q)

theorem radialSatakeCharacter_rational (e : ℂˣ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    radialSatakeCharacter q e ((1 : ℂ) ⊗ₜ[ℚ] T) =
      (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).sum
        (fun x a => (a : ℂ) * (e.val / Radial.Cyclicity.normalization q) ^ ((Borel.Iwasawa.decomposition q).height x 0)) := by
  unfold radialSatakeCharacter normalizedSatake
  rw [AlgHom.comp_apply, AlgHom.comp_apply, HeckeScalarExtension.Iwasawa.complexHecke_tmul, one_smul]
  change SatakeKernel.Iwasawa.evaluateLattice _ (RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.twist _
    ((Borel.Iwasawa.decomposition q).constantTerm (HeckeScalarExtension.Iwasawa.rationalComplexHecke _ T))) = _
  rw [SatakeKernel.Iwasawa.evaluate_twist, SatakeKernel.Iwasawa.evaluate_constantTerm_rational]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun z : ℂ => (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T x : ℂ) * z)
  have h := congrArg (fun u : ℂˣ => (u : ℂ))
    (SatakeParameters.Iwasawa.radialTorusPoint_weight q e ((Borel.Iwasawa.decomposition q).height x) (Borel.Iwasawa.height_sum q x))
  simpa only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.coeHom_apply,
    Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val, SatakeParameters.Iwasawa.normalization_eq_sqrt_cube] using h

theorem radialCharacter_eq_satake
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (e : ℂ) (he : e ≠ 0) :
    Radial.Characters.radialCharacter q hElementaryDivisors e he = radialSatakeCharacter q (Units.mk0 e he) := by
  have hbase (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
      Radial.Characters.radialCharacter q hElementaryDivisors e he ((1 : ℂ) ⊗ₜ[ℚ] T) =
        radialSatakeCharacter q (Units.mk0 e he) ((1 : ℂ) ⊗ₜ[ℚ] T) := by
    change Radial.Characters.radialEigenvalue q hElementaryDivisors e _ = _
    rw [Radial.ConstantTerm.Iwasawa.radialEigenvalue_kernel, radialSatakeCharacter_rational]
    rfl
  apply AlgHom.ext
  intro T
  induction T using TensorProduct.inductionOn with
  | add T U hT hU => simp only [map_add, hT, hU]
  | tmul c T =>
      have ht : c ⊗ₜ[ℚ] T = c • ((1 : ℂ) ⊗ₜ[ℚ] T) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul, map_smul, hbase]

end

/-! Rational coefficients of the actual normalized native SL3 Satake
transform. The normalization is q raised to an integer, and the constant
term is the finite pushforward of the original rational Hecke kernel. -/

open scoped Classical TensorProduct

variable (q : ℕ) [Fact q.Prime]

theorem normalizedSatake_coeff (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (ell : Fin 3 → ℤ) :
    (normalizedSatake q ((1 : ℂ) ⊗ₜ[ℚ] T)).coeff ell =
      (Finsupp.mapDomain (Borel.Iwasawa.decomposition q).height (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T) ell : ℂ) *
        (q : ℂ) ^ (ell 2 - ell 0) := by
  unfold normalizedSatake
  rw [AlgHom.comp_apply, HeckeScalarExtension.Iwasawa.complexHecke_tmul, one_smul, RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.satake_coeff]
  have hc : ((Borel.Iwasawa.decomposition q).constantTerm
      (HeckeScalarExtension.Iwasawa.rationalComplexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T)).coeff ell =
    (Finsupp.mapDomain (Borel.Iwasawa.decomposition q).height (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T) ell : ℂ) := by
    change ((Borel.Iwasawa.decomposition q).pushforward
      (RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (HeckeScalarExtension.Iwasawa.rationalComplexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T))).coeff ell = _
    rw [RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition.pushforward_coeff, SatakeKernel.Iwasawa.rationalComplexHecke_kernel_map,
      Finsupp.mapDomain_mapRange _ _ _ _ (map_add _)]
    rfl
  rw [hc]
  congr 1
  have hs : (Real.sqrt (q : ℝ) : ℂ) ^ (2 : ℤ) = (q : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  rw [← hs, ← zpow_mul]
  congr 1
  simp [RepresentationTheory.Satake.GL3GL.Core.twoRho]
  ring

def rationalSatakeCoefficients (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) : (Fin 3 → ℤ) →₀ ℚ :=
  let f := Finsupp.mapDomain (Borel.Iwasawa.decomposition q).height (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T)
  Finsupp.onFinset f.support (fun ell => f ell * (q : ℚ) ^ (ell 2 - ell 0))
    (fun _ h => Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp h).1)

theorem rationalSatakeCoefficients_cast (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (ell : Fin 3 → ℤ) :
    (rationalSatakeCoefficients q T ell : ℂ) =
      (normalizedSatake q ((1 : ℂ) ⊗ₜ[ℚ] T)).coeff ell := by
  rw [normalizedSatake_coeff]
  simp only [rationalSatakeCoefficients, Finsupp.onFinset_apply, Rat.cast_mul, Rat.cast_zpow,
    Rat.cast_natCast]

theorem normalizedSatake_rational (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    AddMonoidAlgebra.mapRingHom (Fin 3 → ℤ) (algebraMap ℚ ℂ)
      (AddMonoidAlgebra.ofCoeff (rationalSatakeCoefficients q T)) =
        normalizedSatake q ((1 : ℂ) ⊗ₜ[ℚ] T) := by
  ext ell
  exact rationalSatakeCoefficients_cast q T ell

theorem normalizedSatake_coeff_fixed (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q)
    (σ : ℂ ≃ₐ[ℚ] ℂ) (ell : Fin 3 → ℤ) :
    σ ((normalizedSatake q ((1 : ℂ) ⊗ₜ[ℚ] T)).coeff ell) =
      (normalizedSatake q ((1 : ℂ) ⊗ₜ[ℚ] T)).coeff ell := by
  rw [← rationalSatakeCoefficients_cast]
  exact σ.commutes _

theorem rationalSatakeScalar_injective :
    Function.Injective (AddMonoidAlgebra.mapRingHom (Fin 3 → ℤ) (algebraMap ℚ ℂ)) :=
  AddMonoidAlgebra.map_injective _ (algebraMap ℚ ℂ).injective

def descendAlgHom {R A B C : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (i : B →ₐ[R] C) (hi : Function.Injective i) (f : A →ₐ[R] C)
    (g : A → B) (hg : ∀ a, i (g a) = f a) : A →ₐ[R] B where
  toFun := g
  map_zero' := hi (by rw [hg, map_zero, map_zero])
  map_one' := hi (by rw [hg, map_one, map_one])
  map_add' a b := hi (by rw [hg, map_add, map_add, hg, hg])
  map_mul' a b := hi (by rw [hg, map_mul, map_mul, hg, hg])
  commutes' r := hi (by rw [hg, f.commutes, i.commutes])

def complexRationalSatake : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] AddMonoidAlgebra ℂ (Fin 3 → ℤ) :=
  ((RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.satake (Borel.Iwasawa.decomposition q) q (Fact.out : q.Prime).pos
    RepresentationTheory.Satake.GL3GL.Core.twoRho).restrictScalars ℚ).comp (HeckeScalarExtension.Iwasawa.rationalComplexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q))

theorem complexRationalSatake_eq (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    complexRationalSatake q T = normalizedSatake q ((1 : ℂ) ⊗ₜ[ℚ] T) := by
  unfold normalizedSatake
  rw [AlgHom.comp_apply, HeckeScalarExtension.Iwasawa.complexHecke_tmul, one_smul]
  rfl

def rationalSatake : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] AddMonoidAlgebra ℚ (Fin 3 → ℤ) :=
  descendAlgHom
    (AddMonoidAlgebra.mapAlgHom (Fin 3 → ℤ) (Algebra.ofId ℚ ℂ))
    rationalSatakeScalar_injective (complexRationalSatake q)
    (fun T => AddMonoidAlgebra.ofCoeff (rationalSatakeCoefficients q T))
    (fun T => (normalizedSatake_rational q T).trans (complexRationalSatake_eq q T).symm)

theorem rationalSatake_scalar_extension (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    AddMonoidAlgebra.mapRingHom (Fin 3 → ℤ) (algebraMap ℚ ℂ) (rationalSatake q T) =
      normalizedSatake q ((1 : ℂ) ⊗ₜ[ℚ] T) := normalizedSatake_rational q T

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake.Iwasawa
