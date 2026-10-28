import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Iwasawa
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake

/-! # Satake -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Satake.Iwasawa

noncomputable section

/-! The actual normalized GL3 kernel transform restricts to the previously
constructed SL3 transform. Both use the same finite kernel pushforward
and integer-valued modulus normalization. -/

open scoped Classical TensorProduct

variable (q : ℕ) [Fact q.Prime]

theorem normalizedIwasawa_rational_coeff {G : Type*} [Group G] {K : Subgroup G}
    (D : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition K (Fin 3 → ℤ)) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K)
    (ell : Fin 3 → ℤ) :
    (RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.satake D q (Fact.out : q.Prime).pos RepresentationTheory.Satake.GL3GL.Core.twoRho
      (HeckeScalarExtension.Iwasawa.rationalComplexHecke K T)).coeff ell =
      (Finsupp.mapDomain D.height (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T) ell : ℂ) *
        (q : ℂ) ^ (ell 2 - ell 0) := by
  rw [RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.satake_coeff]
  have hc : (D.constantTerm (HeckeScalarExtension.Iwasawa.rationalComplexHecke K T)).coeff ell =
      (Finsupp.mapDomain D.height (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T) ell : ℂ) := by
    change (D.pushforward (RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.kernel K (HeckeScalarExtension.Iwasawa.rationalComplexHecke K T))).coeff ell = _
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

def gl3NormalizedSatake : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[ℂ]
    AddMonoidAlgebra ℂ (Fin 3 → ℤ) :=
  (RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.satake (Iwasawa.gl3Decomposition q) q (Fact.out : q.Prime).pos RepresentationTheory.Satake.GL3GL.Core.twoRho).comp
    (HeckeScalarExtension.Iwasawa.complexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))

theorem gl3NormalizedSatake_coeff (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))
    (ell : Fin 3 → ℤ) :
    (gl3NormalizedSatake q (1 ⊗ₜ[ℚ] T)).coeff ell =
      (Finsupp.mapDomain (Iwasawa.gl3Decomposition q).height (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T) ell : ℂ) *
        (q : ℂ) ^ (ell 2 - ell 0) := by
  unfold gl3NormalizedSatake
  rw [AlgHom.comp_apply, HeckeScalarExtension.Iwasawa.complexHecke_tmul, one_smul]
  exact normalizedIwasawa_rational_coeff q (Iwasawa.gl3Decomposition q) T ell

theorem gl3NormalizedSatake_sl3 {s : ℕ} (v : Fin s) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    gl3NormalizedSatake q (1 ⊗ₜ[ℚ] Retraction.Local.sl3ToGL3Hecke q v T) =
      RadialSatake.Iwasawa.normalizedSatake q (1 ⊗ₜ[ℚ] T) := by
  ext ell
  rw [gl3NormalizedSatake_coeff, RadialSatake.Iwasawa.normalizedSatake_coeff]
  have hk : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (Retraction.Local.sl3ToGL3Hecke q v T) =
      Finsupp.mapDomain (Iwasawa.sl3ToGL3Coset q) (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T) :=
    Iwasawa.sl3ToGL3Hecke_kernel q v T
  rw [hk]
  congr 2
  rw [← Finsupp.mapDomain_comp]
  have hh : (Iwasawa.gl3Decomposition q).height ∘ Iwasawa.sl3ToGL3Coset q = (Borel.Iwasawa.decomposition q).height :=
    funext (Iwasawa.gl3_height_sl3 q)
  rw [hh]

def gl3RationalSatakeCoefficients (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    (Fin 3 → ℤ) →₀ ℚ :=
  let f := Finsupp.mapDomain (Iwasawa.gl3Decomposition q).height (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T)
  Finsupp.onFinset f.support (fun ell => f ell * (q : ℚ) ^ (ell 2 - ell 0))
    (fun _ h => Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp h).1)

theorem gl3RationalSatakeCoefficients_cast (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))
    (ell : Fin 3 → ℤ) :
    (gl3RationalSatakeCoefficients q T ell : ℂ) =
      (gl3NormalizedSatake q (1 ⊗ₜ[ℚ] T)).coeff ell := by
  rw [gl3NormalizedSatake_coeff]
  simp only [gl3RationalSatakeCoefficients, Finsupp.onFinset_apply, Rat.cast_mul,
    Rat.cast_zpow, Rat.cast_natCast]

def gl3ComplexRationalSatake : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[ℚ]
    AddMonoidAlgebra ℂ (Fin 3 → ℤ) :=
  ((RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.satake (Iwasawa.gl3Decomposition q) q (Fact.out : q.Prime).pos
    RepresentationTheory.Satake.GL3GL.Core.twoRho).restrictScalars ℚ).comp (HeckeScalarExtension.Iwasawa.rationalComplexHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))

def gl3RationalSatake : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[ℚ]
    AddMonoidAlgebra ℚ (Fin 3 → ℤ) :=
  RadialSatake.Iwasawa.descendAlgHom
    (AddMonoidAlgebra.mapAlgHom (Fin 3 → ℤ) (Algebra.ofId ℚ ℂ))
    RadialSatake.Iwasawa.rationalSatakeScalar_injective (gl3ComplexRationalSatake q)
    (fun T => AddMonoidAlgebra.ofCoeff (gl3RationalSatakeCoefficients q T)) (fun T => by
      ext ell
      change (gl3RationalSatakeCoefficients q T ell : ℂ) = _
      have hc := gl3RationalSatakeCoefficients_cast q T ell
      unfold gl3NormalizedSatake at hc
      rw [AlgHom.comp_apply, HeckeScalarExtension.Iwasawa.complexHecke_tmul, one_smul] at hc
      exact hc)

theorem gl3RationalSatake_sl3 {s : ℕ} (v : Fin s) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    gl3RationalSatake q (Retraction.Local.sl3ToGL3Hecke q v T) = RadialSatake.Iwasawa.rationalSatake q T := by
  apply RadialSatake.Iwasawa.rationalSatakeScalar_injective
  have hgl (U : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
      AddMonoidAlgebra.mapRingHom (Fin 3 → ℤ) (algebraMap ℚ ℂ) (gl3RationalSatake q U) =
        gl3NormalizedSatake q (1 ⊗ₜ[ℚ] U) := by
    ext ell
    exact gl3RationalSatakeCoefficients_cast q U ell
  rw [hgl, RadialSatake.Iwasawa.rationalSatake_scalar_extension, gl3NormalizedSatake_sl3]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Satake.Iwasawa
