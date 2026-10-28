import OAI.RepresentationTheory.Theta.Geometric.AwayLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinates

/-! # Localized Lattice Maps -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalizedLatticeMaps.TestTransport

noncomputable section

/-! A linear map preserves the lattice with q inverted if and only
if it sends the original integral lattice into that localization. -/

open scoped Classical

variable {V J : Type*} [AddCommGroup V] (L : Submodule ℤ V) (q : ℕ)

def powerLocalizedLattice : Submodule ℤ V :=
  Submodule.span ℤ {x | ∃ n : ℕ, (q : ℤ) ^ n • x ∈ L}

theorem mem_powerLocalizedLattice (x : V) :
    x ∈ powerLocalizedLattice L q ↔ ∃ n : ℕ, (q : ℤ) ^ n • x ∈ L :=
  RepresentationTheory.Theta.Geometric.AwayLattice.mem_power_localized_lattice q L x

theorem lattice_le_powerLocalizedLattice : L ≤ powerLocalizedLattice L q := by
  intro x hx
  exact (mem_powerLocalizedLattice L q x).mpr ⟨0, by simpa using hx⟩

theorem powerLocalizedLattice_map_iff (f : V →ₗ[ℤ] V) :
    (∀ x ∈ powerLocalizedLattice L q, f x ∈ powerLocalizedLattice L q) ↔
      ∀ x ∈ L, f x ∈ powerLocalizedLattice L q := by
  constructor
  · exact fun h x hx => h x (lattice_le_powerLocalizedLattice L q hx)
  · intro h x hx
    obtain ⟨n, hn⟩ := (mem_powerLocalizedLattice L q x).mp hx
    obtain ⟨m, hm⟩ := (mem_powerLocalizedLattice L q _).mp (h _ hn)
    refine (mem_powerLocalizedLattice L q _).mpr ⟨m + n, ?_⟩
    rw [map_smul] at hm
    simpa only [pow_add, mul_smul] using hm

variable [Fintype J] (b : Module.Basis J ℤ L)

theorem linearMap_lattice_mem_iff_basis (M : Submodule ℤ V) (f : V →ₗ[ℤ] V) :
    (∀ x ∈ L, f x ∈ M) ↔ ∀ j, f (b j).val ∈ M := by
  constructor
  · exact fun h j => h _ (b j).property
  · intro h x hx
    have he : (∑ j, b.equivFun ⟨x, hx⟩ j • (b j).val) = x := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg (fun z : L => z.val) (b.sum_equivFun ⟨x, hx⟩)
    rw [← he, map_sum]
    apply M.sum_mem
    intro j _
    rw [map_smul]
    exact M.smul_mem _ (h j)

theorem powerLocalizedLattice_map_iff_basis (f : V →ₗ[ℤ] V) :
    (∀ x ∈ powerLocalizedLattice L q, f x ∈ powerLocalizedLattice L q) ↔
      ∀ j, f (b j).val ∈ powerLocalizedLattice L q :=
  (powerLocalizedLattice_map_iff L q f).trans
    (linearMap_lattice_mem_iff_basis L b (powerLocalizedLattice L q) f)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalizedLatticeMaps.TestTransport
