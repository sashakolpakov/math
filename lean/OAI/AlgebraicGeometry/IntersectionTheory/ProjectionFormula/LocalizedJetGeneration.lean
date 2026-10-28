import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.JetProduct
import Mathlib.RingTheory.Localization.Basic

/-! # Localized Jet Generation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedJetGeneration

noncomputable section

/-! Algebra generators still span all first-order data after localization:
inverting an element whose value is nonzero requires no new tangent direction. -/

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.JetProduct

universe u v w

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]
  (ε : R →ₐ[K] K)

theorem mem_of_mul (V : Submodule K (K × (AugmentedCotangent.ideal ε).Cotangent))
    (h1 : AugmentedCotangent.jet ε 1 ∈ V) (r s : R) (hs : ε s ≠ 0)
    (hprod : AugmentedCotangent.jet ε (r * s) ∈ V) (hmem : AugmentedCotangent.jet ε s ∈ V) : AugmentedCotangent.jet ε r ∈ V := by
  have he : ε s • AugmentedCotangent.jet ε r =
      AugmentedCotangent.jet ε (r * s) - ε r • AugmentedCotangent.jet ε s + (ε r * ε s) • AugmentedCotangent.jet ε 1 := by
    rw [JetProduct.jet_mul]
    abel
  have hm : ε s • AugmentedCotangent.jet ε r ∈ V := by
    rw [he]
    exact V.add_mem (V.sub_mem hprod (V.smul_mem (ε r) hmem))
      (V.smul_mem (ε r * ε s) h1)
  have h := V.smul_mem (ε s)⁻¹ hm
  simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using h

variable {A : Type w} [CommRing A] [Algebra K A] [Algebra A R] [IsScalarTower K A R]

theorem span (M : Submonoid A) [IsLocalization M R]
    (S : Set A) (hS : Algebra.adjoin K S = ⊤) :
    Submodule.span K (insert (AugmentedCotangent.jet ε 1) ((AugmentedCotangent.jet ε ∘ algebraMap A R) '' S)) = ⊤ := by
  let V := Submodule.span K (insert (AugmentedCotangent.jet ε 1) ((AugmentedCotangent.jet ε ∘ algebraMap A R) '' S))
  have h1 : AugmentedCotangent.jet ε 1 ∈ V := Submodule.subset_span (Set.mem_insert _ _)
  have hA : ∀ a : A, AugmentedCotangent.jet ε (algebraMap A R a) ∈ V := by
    have hle : Algebra.adjoin K S ≤
        (JetProduct.subalgebra ε V h1).comap (IsScalarTower.toAlgHom K A R) := by
      apply Algebra.adjoin_le
      intro a ha
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)
    intro a
    exact hle (hS ▸ (show a ∈ (⊤ : Subalgebra K A) from trivial))
  apply top_unique
  intro v _
  obtain ⟨r, rfl⟩ := AugmentedCotangent.jet_surjective ε v
  obtain ⟨⟨a, s⟩, hrs⟩ := IsLocalization.surj M r
  apply mem_of_mul ε V h1 r (algebraMap A R s)
  · exact ((IsLocalization.map_units R s).map ε.toRingHom).ne_zero
  · rw [hrs]
    exact hA a
  · exact hA s

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedJetGeneration
