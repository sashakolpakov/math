import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCotangent
import OAI.AlgebraicGeometry.Divisors.LineBundles.DifferentialCoordinates
import Mathlib.RingTheory.LocalRing.Module

/-! # Section Differentials -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionDifferentials.BundleCycles

noncomputable section

/-! # LineBundleCycles: a smooth local section has actual kernel coordinates with a differential basis -/

open KaehlerDifferential

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A]

def sectionDifference (b : B) : RingHom.ker (algebraMap B A) :=
  ⟨b - algebraMap A B (algebraMap B A b), by
    change algebraMap B A (b - algebraMap A B (algebraMap B A b)) = 0
    rw [map_sub, ← IsScalarTower.algebraMap_apply A B A]
    exact sub_self _⟩

theorem sectionDifference_differential (b : B) : D A B (sectionDifference A B b).val = D A B b := by
  change D A B (b - algebraMap A B (algebraMap B A b)) = _
  rw [map_sub, Derivation.map_algebraMap, sub_zero]

theorem sectionKernelDifferential_span :
    Submodule.span B (Set.range (fun b : RingHom.ker (algebraMap B A) => D A B b.val)) = ⊤ := by
  apply top_unique
  rw [← span_range_derivation A B]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  exact Submodule.subset_span ⟨sectionDifference A B b, sectionDifference_differential A B b⟩

variable [IsLocalRing B] [IsNoetherianRing B] [Algebra.EssFiniteType A B] [Algebra.FormallySmooth A B]

omit [IsNoetherianRing B] in
theorem smoothSection_exists_differentialBasis :
    ∃ (ι : Type) (_ : Finite ι) (v : ι → RingHom.ker (algebraMap B A)) (b : Module.Basis ι B Ω[B⁄A]),
      ∀ i, b i = D A B (v i).val := by
  obtain ⟨ι, v, b, hb⟩ := Module.exists_basis_of_span_of_flat
    (fun r : RingHom.ker (algebraMap B A) => D A B r.val) (sectionKernelDifferential_span A B)
  exact ⟨ι, Module.Finite.finite_basis b, v, b, hb⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionDifferentials.BundleCycles
