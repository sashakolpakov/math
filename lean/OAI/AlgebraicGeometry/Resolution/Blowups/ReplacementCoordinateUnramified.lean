import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations
import Mathlib.Algebra.GroupWithZero.Action.Units

/-! # Replacement Coordinate Unramified -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReplacementCoordinateUnramified.Construction

noncomputable section

/-! A unit coordinate derivative detects an unramified replacement coordinate map. -/

variable {σ K R B : Type*} [Field K] [CommRing R] [CommRing B]
  [Algebra (MvPolynomial σ K) R] [Algebra.Etale (MvPolynomial σ K) R]
  [Algebra K R] [IsScalarTower K (MvPolynomial σ K) R]
  [Algebra K B] [Algebra B R] [IsScalarTower K B R]
  [Fintype σ] [DecidableEq σ]

/-- If a new coordinate has unit derivative in the replaced direction,
retaining all complementary coordinates leaves no relative differentials. -/
theorem formallyUnramified_of_replacement_coordinate (i : σ) (z : R)
    (hz : IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i z))
    (hcoords : ∀ j : σ, i ≠ j → ∃ b : B,
      algebraMap (MvPolynomial σ K) R (MvPolynomial.X j) = algebraMap B R b)
    (hnew : ∃ b : B, z = algebraMap B R b) : Algebra.FormallyUnramified B R := by
  let D : Derivation K R (KaehlerDifferential B R) :=
    (KaehlerDifferential.D B R).restrictScalars K
  have hother : ∀ j : σ, i ≠ j →
      D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X j)) = 0 := by
    intro j hij
    obtain ⟨b, hb⟩ := hcoords j hij
    rw [hb]
    exact (KaehlerDifferential.D B R).map_algebraMap b
  have hDz : D z = 0 := by
    obtain ⟨b, rfl⟩ := hnew
    exact (KaehlerDifferential.D B R).map_algebraMap b
  have hsum : (∑ j : σ, Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) j z •
      D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X j))) =
        Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i z •
          D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X i)) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hother j (Ne.symm hji), smul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have h := Blowups.Etale.ModuleDerivations.Construction.etale_coordinate_module_derivation_expansion (σ := σ) D z
  rw [hDz, hsum] at h
  have hi : D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X i)) = 0 :=
    hz.smul_eq_zero.mp h.symm
  have hcoord : ∀ j : σ, D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X j)) = 0 := by
    intro j
    by_cases hij : i = j
    · subst j
      exact hi
    · exact hother j hij
  have hzero : ∀ x : R, KaehlerDifferential.D B R x = 0 := by
    intro x
    change D x = 0
    rw [Blowups.Etale.ModuleDerivations.Construction.etale_coordinate_module_derivation_expansion (σ := σ) D x]
    apply Finset.sum_eq_zero
    intro j _
    rw [hcoord j, smul_zero]
  have htop : (⊤ : Submodule R (KaehlerDifferential B R)) ≤ ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hzero x
  constructor
  apply (subsingleton_iff_forall_eq (0 : KaehlerDifferential B R)).mpr
  intro x
  exact htop (show x ∈ (⊤ : Submodule R (KaehlerDifferential B R)) from trivial)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReplacementCoordinateUnramified.Construction
