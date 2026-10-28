import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LatticeBounds
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryDivisors

/-! # Superlattice Type -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SuperlatticeType.Construction

noncomputable section

/-!
The full ElementaryDivisors prerequisite classifies bounded superlattices by precisely
the dominant natural kernel exponents of IsogenyQuotient. Negative Smith powers are
retained in the actual lattice formula, fixing the double-coset direction.
-/

open _root_.Module
open scoped Pointwise

universe u

open OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {d : ℕ}

def uniformizerPowerLattice (π : R) (hπ : Irreducible π) (m : ℤ)
    (L : Submodule R (Fin d → K)) : Submodule R (Fin d → K) :=
  (Units.mk0 (algebraMap R K π) (OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero hπ)) ^ m • L

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem diagonalLattice_const
    (π : R) (hπ : Irreducible π) (e : Basis (Fin d) K (Fin d → K)) (m : ℤ) :
    LatticeBounds.Construction.diagonalLattice π e (fun _ => m) =
      uniformizerPowerLattice π hπ m (Submodule.span R (Set.range e)) := by
  let z := (Units.mk0 (algebraMap R K π) (OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero hπ)) ^ m
  have hgen : (fun i => (algebraMap R K π) ^ m • e i) = (fun i => z • e i) := by
    funext i
    simp [z, Units.smul_def]
  change Submodule.span R (Set.range fun i => (algebraMap R K π) ^ m • e i) = z • _
  rw [hgen, Set.range_smul, ← Submodule.smul_span]
  rfl

/-- A bounded superlattice has unique dominant natural kernel exponents,
using ElementaryDivisors in its complete four-clause form. -/
theorem bounded_superlattice_type_from_ElementaryDivisors
    (π : R) (hπ : Irreducible π)
    (L M : Submodule R (Fin d → K))
    [Submodule.IsLattice K L] [Submodule.IsLattice K M]
    (h : ℕ) (hlower : L ≤ M)
    (hupper : M ≤ uniformizerPowerLattice π hπ (-(h : ℤ)) L)
    (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput.{u}) :
    ∃! a : Fin d → ℕ,
      Antitone a ∧ (∀ i, a i ≤ h) ∧
      ∃ e : Basis (Fin d) K (Fin d → K),
        L = Submodule.span R (Set.range e) ∧
        M = LatticeBounds.Construction.diagonalLattice π e (fun i => -(a i : ℤ)) := by
  obtain ⟨b, ⟨hb, e, heL, heM⟩, hub⟩ := (h_ElementaryDivisors (R := R) (K := K)).1 π hπ L M
  change M = LatticeBounds.Construction.diagonalLattice π e b at heM
  have hlow : Submodule.span R (Set.range e) ≤ LatticeBounds.Construction.diagonalLattice π e b := by
    rw [← heL, ← heM]
    exact hlower
  have hupp : LatticeBounds.Construction.diagonalLattice π e b ≤ LatticeBounds.Construction.diagonalLattice π e (fun _ => -(h : ℤ)) := by
    rw [← heM, diagonalLattice_const π hπ, ← heL]
    exact hupper
  have hbounds := LatticeBounds.Construction.superlattice_exponent_bounds π hπ e b h hlow hupp
  let a : Fin d → ℕ := fun i => (-b i).toNat
  have ha (i : Fin d) : (a i : ℤ) = -b i := Int.toNat_of_nonneg (hbounds i).1
  have haanti : Antitone a := by
    intro i j hij
    apply Int.ofNat_le.mp
    rw [ha, ha]
    exact neg_le_neg (hb hij)
  have habound (i : Fin d) : a i ≤ h := by
    apply Int.ofNat_le.mp
    rw [ha]
    exact (hbounds i).2
  have hneg : (fun i => -(a i : ℤ)) = b := by
    funext i
    rw [ha, neg_neg]
  refine ⟨a, ⟨haanti, habound, e, heL, ?_⟩, ?_⟩
  · rw [hneg]
    exact heM
  · rintro a' ⟨ha'anti, _, e', he'L, he'M⟩
    have heq : (fun i => -(a' i : ℤ)) = b := by
      apply hub
      refine ⟨?_, e', he'L, he'M⟩
      intro i j hij
      exact neg_le_neg (Int.ofNat_le.mpr (ha'anti hij))
    funext i
    have hi := congrFun heq i
    have hi' := ha i
    omega

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SuperlatticeType.Construction
