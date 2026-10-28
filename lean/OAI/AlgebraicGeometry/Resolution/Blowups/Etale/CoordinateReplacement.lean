import OAI.AlgebraicGeometry.Resolution.Blowups.ReplacementCoordinateUnramified
import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateFrame

/-! # Coordinate Replacement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateReplacement.Construction

noncomputable section

/-! Replacing one coordinate of an étale chart while keeping every complement fixed. -/

variable {σ K R : Type*} [Field K] [CommRing R]
  [Algebra (MvPolynomial σ K) R] [Algebra.Etale (MvPolynomial σ K) R]
  [Algebra K R] [IsScalarTower K (MvPolynomial σ K) R] [DecidableEq σ]

def replacementCoordinateFamily (i : σ) (z : R) : Option {j : σ // i ≠ j} → R :=
  AdaptedEtaleFrame.Construction.transverseExtendedCoordinates
    (fun j : {j : σ // i ≠ j} => algebraMap (MvPolynomial σ K) R (MvPolynomial.X j.val)) z

def replacementCoordinateMap (i : σ) (z : R) :
    MvPolynomial (Option {j : σ // i ≠ j}) K →ₐ[K] R :=
  MvPolynomial.aeval (replacementCoordinateFamily (K := K) i z)

omit [Algebra.Etale (MvPolynomial σ K) R] [IsScalarTower K (MvPolynomial σ K) R]
  [DecidableEq σ] in
theorem replacementCoordinateMap_none (i : σ) (z : R) :
    replacementCoordinateMap (K := K) i z (MvPolynomial.X none) = z :=
  MvPolynomial.aeval_X _ _

omit [Algebra.Etale (MvPolynomial σ K) R] [IsScalarTower K (MvPolynomial σ K) R]
  [DecidableEq σ] in
theorem replacementCoordinateMap_some (i : σ) (z : R) (j : {j : σ // i ≠ j}) :
    replacementCoordinateMap (K := K) i z (MvPolynomial.X (some j)) =
      algebraMap (MvPolynomial σ K) R (MvPolynomial.X j.val) :=
  MvPolynomial.aeval_X _ _

variable [Fintype σ]

/-- A unit coordinate partial derivative makes the replacement map étale.
Every other original coordinate is retained exactly. -/
theorem replacementCoordinateMap_etale (i : σ) (z : R)
    (hz : IsUnit (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i z)) :
    (replacementCoordinateMap (K := K) i z).toRingHom.Etale := by
  let u : Rˣ := hz.unit
  have hu : (u : R) = DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i z := hz.unit_spec
  let E : Derivation K R R := (u⁻¹ : Rˣ) • DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i
  let D : {j : σ // i ≠ j} → Derivation K R R := fun j => DifferentialEquation.Construction.etaleRelativePartial (K := K) j.val
  let w : {j : σ // i ≠ j} → R := fun j =>
    algebraMap (MvPolynomial σ K) R (MvPolynomial.X j.val)
  have hEz : E z = 1 := by
    change (u⁻¹ : Rˣ) • DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i z = 1
    rw [← hu]
    change (↑u⁻¹ : R) * ↑u = 1
    exact Units.inv_mul u
  have hEw : ∀ j, E (w j) = 0 := by
    intro j
    change (u⁻¹ : Rˣ) • DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i
      (algebraMap (MvPolynomial σ K) R (MvPolynomial.X j.val)) = 0
    rw [TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_right j.property, smul_zero]
  have hD : ∀ j l, D j (w l) = if j = l then 1 else 0 := by
    intro j l
    simpa only [Subtype.ext_iff] using TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X (K := K) (S := R) j.val l.val
  let Q := MvPolynomial (Option {j : σ // i ≠ j}) K
  let γ : Q →ₐ[K] R := replacementCoordinateMap i z
  let : Algebra Q R := γ.toRingHom.toAlgebra
  let : IsScalarTower K Q R := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap K R a = γ (algebraMap K Q a)
    exact (γ.commutes a).symm)
  have hmap : ∀ j : Option {j : σ // i ≠ j},
      algebraMap Q R (MvPolynomial.X j) = AdaptedEtaleFrame.Construction.transverseExtendedCoordinates w z j := by
    intro j
    change γ (MvPolynomial.X j) = AdaptedEtaleFrame.Construction.transverseExtendedCoordinates w z j
    exact MvPolynomial.aeval_X _ _
  let F := AdaptedEtaleFrame.Construction.transverseExtendedDerivations D E z
  have hF : ∀ j l, F j (algebraMap Q R (MvPolynomial.X l)) =
      if j = l then 1 else 0 := by
    intro j l
    rw [hmap]
    exact AdaptedEtaleFrame.Construction.transverseExtendedDerivations_dual D w E z hD hEz hEw j l
  let : Algebra.Smooth K (MvPolynomial σ K) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth K R := Algebra.Smooth.comp K (MvPolynomial σ K) R
  let : Algebra.Smooth Q R := Blowups.Smooth.CoordinateFrame.Construction.smooth_over_coordinate_frame F hF
  let : Algebra.FormallyUnramified Q R := ReplacementCoordinateUnramified.Construction.formallyUnramified_of_replacement_coordinate
    (B := Q) i z hz (by
      intro j hij
      refine ⟨MvPolynomial.X (some ⟨j, hij⟩), ?_⟩
      exact (hmap (some ⟨j, hij⟩)).symm) ⟨MvPolynomial.X none, (hmap none).symm⟩
  have he : Algebra.Etale Q R :=
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩
  change (algebraMap Q R).Etale
  exact RingHom.etale_algebraMap.mpr he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateReplacement.Construction
