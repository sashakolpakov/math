import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairedBlocks
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local

/-! # Self Dual Block Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SelfDualBlockLattices

noncomputable section

/-! Self-duality of the full split lattice forces the exact duality
of opposite blocks, including inverse scaling by the multiplier. -/

open scoped BigOperators Pointwise

variable {R K V I : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem single_mem_pi_submodule_iff (L : I → Submodule R V) (i : I) (x : V) :
    Pi.single i x ∈ Submodule.pi Set.univ L ↔ x ∈ L i := by
  constructor
  · intro h
    have hi : (Pi.single i x : I → V) i ∈ L i := h i (Set.mem_univ i)
    simpa only [Pi.single_eq_same] using hi
  · intro hx j _
    change (Pi.single i x : I → V) j ∈ L j
    by_cases hj : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hx
    · simpa only [Pi.single_eq_of_ne hj] using (L j).zero_mem

variable (B : LinearMap.BilinForm K (I → V)) (τ : I → I) (hτ : Function.Injective τ)
  (horth : ∀ i j, i ≠ τ j → ∀ x y, B (Pi.single i x) (Pi.single j y) = 0)

include hτ horth in
theorem oppositeBlockPairing_whole_value (i : I) (x : V) (z : I → V) :
    B (Pi.single (τ i) x) z = PairedBlocks.oppositeBlockPairing B τ i x (z i) := by
  conv_lhs => rw [← LinearMap.sum_single_apply (fun _ : I => V) z, map_sum]
  apply Finset.sum_eq_single i
  · intro j _ hj
    exact horth (τ i) j (fun h => hj (hτ h).symm) x (z j)
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

include hτ horth in
theorem oppositeBlockPairing_dual_iff_single (L : I → Submodule R V) (i : I) (x : V) :
    x ∈ (PairedBlocks.oppositeBlockPairing B τ i).dualSubmodule (L i) ↔
      Pi.single (τ i) x ∈ B.dualSubmodule (Submodule.pi Set.univ L) := by
  constructor
  · intro hx z hz
    rw [oppositeBlockPairing_whole_value B τ hτ horth i x z]
    exact hx (z i) (hz i (Set.mem_univ i))
  · intro hx y hy
    exact hx (Pi.single i y) ((single_mem_pi_submodule_iff L i y).mpr hy)

include hτ horth in
theorem oppositeBlockLattice_of_self_dual (L : I → Submodule R V)
    (hL : B.dualSubmodule (Submodule.pi Set.univ L) = Submodule.pi Set.univ L) (i : I) :
    L (τ i) = (PairedBlocks.oppositeBlockPairing B τ i).dualSubmodule (L i) := by
  ext x
  rw [oppositeBlockPairing_dual_iff_single B τ hτ horth L i x, hL,
    single_mem_pi_submodule_iff]

include hτ horth in
theorem oppositeBlockLattice_of_scaled_self_dual (m : Kˣ) (L : I → Submodule R V)
    (hL : ((m : K) • B).dualSubmodule (Submodule.pi Set.univ L) = Submodule.pi Set.univ L) (i : I) :
    L (τ i) = m⁻¹ • (PairedBlocks.oppositeBlockPairing B τ i).dualSubmodule (L i) := by
  have hscaled : ∀ a b, a ≠ τ b → ∀ x y,
      ((m : K) • B) (Pi.single a x) (Pi.single b y) = 0 := by
    intro a b hab x y
    change (m : K) * B (Pi.single a x) (Pi.single b y) = 0
    rw [horth a b hab x y, mul_zero]
  have hblock : PairedBlocks.oppositeBlockPairing ((m : K) • B) τ i = (m : K) • PairedBlocks.oppositeBlockPairing B τ i := by
    ext x y
    rfl
  have h := oppositeBlockLattice_of_self_dual ((m : K) • B) τ hτ hscaled L hL i
  rw [hblock] at h
  exact h.trans (Local.oppositeLattice_eq_inverse_smul (PairedBlocks.oppositeBlockPairing B τ i) m (L i))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SelfDualBlockLattices
