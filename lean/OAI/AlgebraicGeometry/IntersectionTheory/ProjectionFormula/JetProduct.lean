import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent

/-! # Jet Product -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.JetProduct

noncomputable section

/-! Product identities for first-order data at a rational point. -/

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent

universe u v

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]
  (ε : R →ₐ[K] K)

theorem differential_mul (r s : R) :
    AugmentedCotangent.differential ε (r * s) = ε r • AugmentedCotangent.differential ε s + ε s • AugmentedCotangent.differential ε r := by
  change (AugmentedCotangent.ideal ε).toCotangent (AugmentedCotangent.center ε (r * s)) =
    ((AugmentedCotangent.ideal ε).toCotangent.restrictScalars K) (ε r • AugmentedCotangent.center ε s) +
      ((AugmentedCotangent.ideal ε).toCotangent.restrictScalars K) (ε s • AugmentedCotangent.center ε r)
  rw [← map_add]
  apply (AugmentedCotangent.ideal ε).toCotangent_eq.mpr
  change r * s - algebraMap K R (ε (r * s)) -
    (ε r • (s - algebraMap K R (ε s)) + ε s • (r - algebraMap K R (ε r))) ∈ (AugmentedCotangent.ideal ε) ^ 2
  rw [pow_two]
  convert (AugmentedCotangent.ideal ε).mul_mem_mul (AugmentedCotangent.center ε r).property (AugmentedCotangent.center ε s).property using 1
  dsimp [AugmentedCotangent.center]
  simp only [map_mul, Algebra.smul_def]
  ring

theorem jet_mul (r s : R) :
    AugmentedCotangent.jet ε (r * s) = ε r • AugmentedCotangent.jet ε s + ε s • AugmentedCotangent.jet ε r - (ε r * ε s) • AugmentedCotangent.jet ε 1 := by
  apply Prod.ext
  · change ε (r * s) = ε r * ε s + ε s * ε r - (ε r * ε s) * ε 1
    simp [mul_comm]
  · change AugmentedCotangent.differential ε (r * s) =
      ε r • AugmentedCotangent.differential ε s + ε s • AugmentedCotangent.differential ε r - (ε r * ε s) • AugmentedCotangent.differential ε 1
    have h1 : AugmentedCotangent.differential ε 1 = 0 := by
      simpa only [map_one] using AugmentedCotangent.differential_constant ε 1
    rw [h1, smul_zero, sub_zero, differential_mul]

theorem jet_constant (c : K) : AugmentedCotangent.jet ε (algebraMap K R c) = c • AugmentedCotangent.jet ε 1 := by
  rw [← map_smul]
  congr 1
  exact ((Algebra.smul_def c (1 : R)).trans (mul_one _)).symm

def subalgebra (V : Submodule K (K × (AugmentedCotangent.ideal ε).Cotangent)) (h1 : AugmentedCotangent.jet ε 1 ∈ V) : Subalgebra K R where
  carrier := {r | AugmentedCotangent.jet ε r ∈ V}
  algebraMap_mem' c := by
    change AugmentedCotangent.jet ε (algebraMap K R c) ∈ V
    rw [jet_constant]
    exact V.smul_mem c h1
  zero_mem' := by simp
  one_mem' := h1
  add_mem' {r s} hr hs := by
    change AugmentedCotangent.jet ε (r + s) ∈ V
    rw [map_add]
    exact V.add_mem hr hs
  mul_mem' {r s} hr hs := by
    change AugmentedCotangent.jet ε (r * s) ∈ V
    rw [jet_mul]
    exact V.sub_mem (V.add_mem (V.smul_mem (ε r) hs) (V.smul_mem (ε s) hr))
      (V.smul_mem (ε r * ε s) h1)

theorem span_of_adjoin_eq_top (S : Set R) (hS : Algebra.adjoin K S = ⊤) :
    Submodule.span K (insert (AugmentedCotangent.jet ε 1) (AugmentedCotangent.jet ε '' S)) = ⊤ := by
  let V := Submodule.span K (insert (AugmentedCotangent.jet ε 1) (AugmentedCotangent.jet ε '' S))
  have h1 : AugmentedCotangent.jet ε 1 ∈ V := Submodule.subset_span (Set.mem_insert _ _)
  have hle : Algebra.adjoin K S ≤ subalgebra ε V h1 := by
    apply Algebra.adjoin_le
    intro r hr
    exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨r, hr, rfl⟩)
  apply top_unique
  intro v _
  obtain ⟨r, rfl⟩ := AugmentedCotangent.jet_surjective ε v
  exact hle (hS ▸ (show r ∈ (⊤ : Subalgebra K R) from trivial))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.JetProduct
