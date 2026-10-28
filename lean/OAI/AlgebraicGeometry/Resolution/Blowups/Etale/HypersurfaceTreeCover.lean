import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineEtaleControlTree
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Hypersurface Tree Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceTreeCover.Construction

noncomputable section

/-! Completing a finite hypersurface refinement cover by its terminal complement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k]

/-- A finite étale family covering the hypersurface, together with its
already constructed child trees, gives a full ambient tree. The complementary
principal open is terminal and introduces no additional blowup depth. -/
theorem exists_control_tree_of_hypersurface_cover
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    (J : Ideal R) (z : R) (n m : ℕ) (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ι : Type u) [Fintype ι] (S : ι → CommRingCat.{u}) [∀ i, Algebra k (S i)]
    (f : ∀ i, R →ₐ[k] S i) (hf : ∀ i, (f i).toRingHom.Etale)
    (hcover : ∀ p : PrimeSpectrum R, z ∈ p.asIdeal →
      ∃ i, ∃ q : PrimeSpectrum (S i), PrimeSpectrum.comap (f i).toRingHom q = p)
    (children : ∀ i, Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) (S i) (J.map (f i).toRingHom))
    (hdepth : ∀ i, (children i).blowupDepth ≤ m) :
    ∃ T : Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R J, T.blowupDepth ≤ m := by
  classical
  let A : Option ι → CommRingCat.{u}
    | none => .of (Localization.Away z)
    | some i => S i
  let aA : ∀ j, Algebra k (A j) := by
    intro j
    cases j with
    | none => exact inferInstanceAs (Algebra k (Localization.Away z))
    | some i => exact inferInstanceAs (Algebra k (S i))
  let aInst : ∀ j, Algebra k (A j) := aA
  let g : ∀ j, R →ₐ[k] A j := by
    intro j
    cases j with
    | none => exact IsScalarTower.toAlgHom k R (Localization.Away z)
    | some i => exact f i
  have hg : ∀ j, (g j).toRingHom.Etale := by
    intro j
    cases j with
    | none => exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway z)
    | some i => exact hf i
  have hcov (p : PrimeSpectrum R) : ∃ j, ∃ q : PrimeSpectrum (A j),
      PrimeSpectrum.comap (g j).toRingHom q = p := by
    by_cases hp : z ∈ p.asIdeal
    · obtain ⟨i, q, hq⟩ := hcover p hp
      exact ⟨some i, q, hq⟩
    · obtain ⟨q, hq⟩ := RefinementHelpers.Construction.exists_localization_away_prime z p hp
      exact ⟨none, q, hq⟩
  let next : ∀ j, Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) (A j) (J.map (g j).toRingHom) := by
    intro j
    cases j with
    | none =>
        apply Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree.terminal
        rw [Nat.add_sub_cancel, ← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k (g none) (hg none) J n]
        apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (g none).toRingHom hz)
        change IsUnit (algebraMap R (Localization.Away z) z)
        exact IsLocalization.Away.algebraMap_isUnit z
    | some i => exact children i
  refine ⟨.refineEtale (Option ι) A g hg hcov next, ?_⟩
  change (Finset.univ.sup fun j => (next j).blowupDepth) ≤ m
  apply Finset.sup_le
  intro j _
  cases j with
  | none => exact Nat.zero_le _
  | some i => exact hdepth i

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceTreeCover.Construction
