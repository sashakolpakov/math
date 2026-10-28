import OAI.NumberTheory.Quaternion.Arithmetic.LocalGaloisNormCurve
import OAI.NumberTheory.Quaternion.Arithmetic.IntegralWeightPoints
import OAI.NumberTheory.Quaternion.Arithmetic.GaloisNormMatrixProduct

/-! # Rational Norm Curve Values -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.RationalNormCurveValues

noncomputable section

section

/-! At a base-field parameter for which the affine coefficient is a
unit, the local norm curve is the image of an actual rational point. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.Matrix

variable {F E : Type} {K A : Type*} [Field F] [Field E] [CharZero E]
  [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
  [NontriviallyNormedField K] [Algebra F K] [NormedCommRing A]
  [Algebra F A] [NormedAlgebra K A] [IsScalarTower F K A] {n : ℕ}

omit [IsGalois F E] in
theorem local_norm_curve_eq_mapped_norm (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (B : ArithmeticGroups.Lattices.Algebraic.SL n E) (m : Fin n → ℤ)
    (hLie : MappedWeightCurves.integerWeightMatrix B m ∈
      ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)))
    (f : E →ₐ[F] A) (a : E) (r : F) (u : Eˣ)
    (hu : (u : E) = 1 + algebraMap F E r * a)
    (hc : ∀ σ τ : E ≃ₐ[F] E,
      Commute (GaloisPoints.galoisPointsHom G σ (IntegralWeightPoints.integralWeightPoint G B m hLie u))
        (GaloisPoints.galoisPointsHom G τ (IntegralWeightPoints.integralWeightPoint G B m hLie u))) :
    LocalGaloisNormCurve.localGaloisNormCurve (K := K) f B a m (algebraMap F K r) =
      (PolynomialGaloisNorm.matrixPointsHom G (algebraMap F E)
        (GaloisNorm.galoisPointNorm G (IntegralWeightPoints.integralWeightPoint G B m hLie u) hc)).map f := by
  apply Eq.trans ?_ (GaloisNormMatrixProduct.galoisPointNorm_mapped_matrix f.toRingHom G _ hc).symm
  unfold LocalGaloisNormCurve.localGaloisNormCurve
  congr 1
  apply List.map_congr_left
  intro σ _
  rw [IntegralWeightPoints.integralWeightPoint_matrix]
  apply MappedWeightCurves.mappedWeightCurve_at_unit
  change (f.comp σ.toAlgHom) u = 1 + algebraMap F K r • (f.comp σ.toAlgHom) a
  rw [hu, map_add, map_one, map_mul, AlgHom.commutes, Algebra.smul_def,
    IsScalarTower.algebraMap_apply F K A]

theorem rational_norm_curve_value (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Matrix (Fin n) (Fin n) F) (B : ArithmeticGroups.Lattices.Algebraic.SL n E) (m : Fin n → ℤ)
    (hLie : MappedWeightCurves.integerWeightMatrix B m ∈
      ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)))
    (hpoly : ∀ u : Eˣ, ∃ p : Polynomial E, Polynomial.aeval (S.map (algebraMap F E)) p =
      (B : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (fun i => ((u ^ m i : Eˣ) : E)) *
        ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n E) : Matrix (Fin n) (Fin n) E))
    (f : E →ₐ[F] A) (a : E) (r : F) (u : Eˣ)
    (hu : (u : E) = 1 + algebraMap F E r * a) :
    ∃ g : G.RationalPoints, LocalGaloisNormCurve.localGaloisNormCurve (K := K) f B a m (algebraMap F K r) =
      (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F A) := by
  let q := IntegralWeightPoints.integralWeightPoint G B m hLie u
  obtain ⟨p, hp⟩ := hpoly u
  have hpq : Polynomial.aeval (S.map (algebraMap F E)) p =
      PolynomialGaloisNorm.matrixPointsHom G (algebraMap F E) q := hp.trans (IntegralWeightPoints.integralWeightPoint_matrix G B m hLie u).symm
  let hc := PolynomialGaloisNorm.galois_orbit_commute_of_polynomial G S q p hpq
  obtain ⟨g, hg⟩ := GaloisNorm.galoisPointNorm_descends G q hc
  refine ⟨g, ?_⟩
  calc
    LocalGaloisNormCurve.localGaloisNormCurve (K := K) f B a m (algebraMap F K r) =
        (PolynomialGaloisNorm.matrixPointsHom G (algebraMap F E) (GaloisNorm.galoisPointNorm G q hc)).map f :=
      local_norm_curve_eq_mapped_norm G B m hLie f a r u hu hc
    _ = (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F A) := by
      rw [← hg]
      ext i j
      exact f.commutes (g.val i j)

end

/-! All local coefficient algebras evaluate a Galois norm to the same
rational point. A local unit condition guarantees that the global
affine parameter is nonzero. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.Matrix

section

variable {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E] {ι : Type*} {K A : ι → Type*}
  [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra F (K i)]
  [∀ i, NormedCommRing (A i)] [∀ i, Algebra F (A i)] [∀ i, NormedAlgebra (K i) (A i)]
  [∀ i, IsScalarTower F (K i) (A i)] {n : ℕ}

theorem simultaneous_rational_norm_curve_values (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Matrix (Fin n) (Fin n) F) (B : ArithmeticGroups.Lattices.Algebraic.SL n E) (m : Fin n → ℤ)
    (hLie : MappedWeightCurves.integerWeightMatrix B m ∈
      ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)))
    (hpoly : ∀ u : Eˣ, ∃ p : Polynomial E, Polynomial.aeval (S.map (algebraMap F E)) p =
      (B : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (fun i => ((u ^ m i : Eˣ) : E)) *
        ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n E) : Matrix (Fin n) (Fin n) E))
    (f : ∀ i, E →ₐ[F] A i) (a : E) (r : F) (u : Eˣ)
    (hu : (u : E) = 1 + algebraMap F E r * a) :
    ∃ g : G.RationalPoints, ∀ i,
      LocalGaloisNormCurve.localGaloisNormCurve (K := K i) (f i) B a m (algebraMap F (K i) r) =
        (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (A i)) := by
  let q := IntegralWeightPoints.integralWeightPoint G B m hLie u
  obtain ⟨p, hp⟩ := hpoly u
  have hpq : Polynomial.aeval (S.map (algebraMap F E)) p =
      PolynomialGaloisNorm.matrixPointsHom G (algebraMap F E) q := hp.trans (IntegralWeightPoints.integralWeightPoint_matrix G B m hLie u).symm
  let hc := PolynomialGaloisNorm.galois_orbit_commute_of_polynomial G S q p hpq
  obtain ⟨g, hg⟩ := GaloisNorm.galoisPointNorm_descends G q hc
  refine ⟨g, fun i => ?_⟩
  apply (local_norm_curve_eq_mapped_norm G B m hLie (f i) a r u hu hc).trans
  rw [← hg]
  ext j k
  exact (f i).commutes (g.val j k)

end

theorem global_affine_isUnit_of_local {F E K A : Type*} [Field F] [Field E] [Algebra F E]
    [Field K] [Algebra F K] [CommRing A] [Nontrivial A] [Algebra F A] [Algebra K A]
    [IsScalarTower F K A] (f : E →ₐ[F] A) (a : E) (r : F)
    (h : IsUnit (1 + algebraMap F K r • f a)) : IsUnit (1 + algebraMap F E r * a) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have he : f (1 + algebraMap F E r * a) = 1 + algebraMap F K r • f a := by
    rw [map_add, map_one, map_mul, f.commutes, Algebra.smul_def,
      IsScalarTower.algebraMap_apply F K A]
  rw [hz, map_zero] at he
  exact not_isUnit_zero (he.symm ▸ h)

end

end OAI.NumberTheory.Quaternion.Arithmetic.RationalNormCurveValues
