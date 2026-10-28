import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.GroupTheory.OrderOfElement

/-! # Power Lie -/

namespace OAI.AlgebraicGeometry.AbelianVariety.PowerLie.Constructions.ExteriorCohomology

noncomputable section

/-!
# Power maps and connectedness for ExteriorCohomology

The derivative of the n-th power map at the identity is multiplication by n.
A compact locally connected commutative group whose positive power maps are
surjective is connected, since its finite component quotient is then trivial.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

section Derivative
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]

theorem mfderiv_pow_one (n : ℕ) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun g : G => g ^ n) 1 v = (n : ℝ) • v := by
  induction n with
  | zero =>
      have hf : (fun g : G => g ^ 0) = (fun _ => (1 : G)) := by funext g; simp
      have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun g : G => g ^ 0) 1 = (0 : E →L[ℝ] E) := by
        rw [hf, mfderiv_const]
        rfl
      have hv := congrArg (fun L : E →L[ℝ] E => L v) hd
      simpa only [Nat.cast_zero, zero_smul] using! hv
  | succ n ih =>
      have hs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun g : G => g ^ n) 1 :=
        (contMDiff_pow (I := 𝓘(ℝ, E)) (n := ∞) n).mdifferentiableAt (by simp)
      have hc := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (I'' := 𝓘(ℝ, E)) (1 : G)
        ((contMDiff_mul 𝓘(ℝ, E) ∞).mdifferentiableAt (by simp))
        (hs.prodMk mdifferentiableAt_id)
      have he : (fun p : G × G => p.1 * p.2) ∘ (fun g : G => (g ^ n, id g)) =
          (fun g : G => g ^ (n + 1)) := by funext g; exact (pow_succ g n).symm
      rw [he, one_pow] at hc
      have hp := mfderiv_prodMk (I := 𝓘(ℝ, E)) hs mdifferentiableAt_id
      rw [hp, mfderiv_id] at hc
      have hv := congrArg (fun f : E →L[ℝ] E => f v) hc
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun g : G => g ^ (n + 1)) 1 v =
        mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (fun p : G × G => p.1 * p.2)
          (1, 1) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun g : G => g ^ n) 1 v, v) at hv
      have hz := hv.trans (InvariantClosed.Constructions.ExteriorCohomology.mfderiv_mul_one (E := E) (G := G)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun g : G => g ^ n) 1 v) v)
      rw [ih] at hz
      simpa only [Nat.cast_add, Nat.cast_one, add_smul, one_smul] using hz

theorem mfderiv_pow_one_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun g : G => g ^ n) 1) := by
  intro v w h
  have he : (n : ℝ) • v = (n : ℝ) • w :=
    (mfderiv_pow_one (E := E) (G := G) n v).symm.trans
      (h.trans (mfderiv_pow_one (E := E) (G := G) n w))
  exact smul_right_injective (M := E) (show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hn) he

end Derivative

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyConnectedSpace G]

theorem connectedSpace_of_surjective_positive_powers
    (hp : ∀ n : ℕ, n ≠ 0 → Function.Surjective (fun g : G => g ^ n)) : ConnectedSpace G := by
  let N := Subgroup.connectedComponentOfOne G
  let : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology isOpen_connectedComponent
  let : Finite (G ⧸ N) := finite_of_compact_of_discrete
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hmem (g : G) : g ∈ N := by
    obtain ⟨h, hh⟩ := hp (Fintype.card (G ⧸ N)) (Fintype.card_ne_zero) g
    apply (QuotientGroup.eq_one_iff g).mp
    rw [← hh, QuotientGroup.mk_pow]
    exact pow_card_eq_one
  apply connectedSpace_iff_connectedComponent.mpr
  exact ⟨(1 : G), Set.eq_univ_of_forall hmem⟩

end

end OAI.AlgebraicGeometry.AbelianVariety.PowerLie.Constructions.ExteriorCohomology
