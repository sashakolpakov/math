import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DiagonalCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.RealCoordinates

/-! # Bilinear Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BilinearCoordinates.Construction

noncomputable section

/-! Integral bracket coordinates are equivalent to integral values
on basis pairs, hence to preservation of the basis lattice by the bracket. -/

open Set
open scoped Classical

theorem mem_integralRealCoordinates_iff {ι : Type*} (x : ι → ℝ) :
    x ∈ RealCoordinates.Construction.integralRealCoordinates ι ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
  constructor
  · rintro ⟨z, rfl⟩ i
    exact ⟨z i, rfl⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

theorem integral_bilinear_coordinates_iff
    {L ι : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] [Fintype ι]
    (b : Module.Basis ι ℝ L) (B : L →L[ℝ] L →L[ℝ] L) :
    Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b B ∈ RealCoordinates.Construction.integralRealCoordinates (ι × ι × ι) ↔
      ∀ i j, B (b i) (b j) ∈ Submodule.span ℤ (Set.range b) := by
  rw [mem_integralRealCoordinates_iff]
  constructor
  · intro h i j
    apply (b.mem_span_iff_repr_mem ℤ _).mpr
    intro l
    exact h (i, j, l)
  · rintro h ⟨i, j, l⟩
    exact (b.mem_span_iff_repr_mem ℤ _).mp (h i j) l

theorem bilinear_basis_lattice_mem
    {L ι : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    (b : Module.Basis ι ℝ L) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : ∀ i j, B (b i) (b j) ∈ Submodule.span ℤ (Set.range b))
    (x y : L) (hx : x ∈ Submodule.span ℤ (Set.range b))
    (hy : y ∈ Submodule.span ℤ (Set.range b)) :
    B x y ∈ Submodule.span ℤ (Set.range b) := by
  let Λ := Submodule.span ℤ (Set.range b)
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hB i j
    | zero => simpa only [map_zero] using Λ.zero_mem
    | add x y _ _ hxy hyy => simpa only [map_add] using Λ.add_mem hxy hyy
    | smul z y _ ih => simpa only [map_zsmul] using Λ.smul_mem z ih
  | zero => simpa only [map_zero, zero_apply] using Λ.zero_mem
  | add x z _ _ ihx ihz => simpa only [map_add, add_apply] using Λ.add_mem ihx ihz
  | smul z x _ ih => simpa only [map_zsmul, smul_apply] using Λ.smul_mem z ih

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BilinearCoordinates.Construction
