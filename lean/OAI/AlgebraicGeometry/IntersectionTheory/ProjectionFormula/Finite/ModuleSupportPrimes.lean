import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
import Mathlib.RingTheory.Spectrum.Prime.Module

/-! # Module Support Primes -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ModuleSupportPrimes

noncomputable section

/-! A finite module over a Noetherian ring has a fixed finite set
of support primes whose specialization closures cover its entire support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

theorem exists_data (R : Type) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat R) [Module.Finite R M] :
    ∃ F : Finset (PrimeSpectrum R),
      (∀ v ∈ F, v ∈ Module.support R M) ∧
      ∀ w ∈ Module.support R M, ∃ v ∈ F, v.asIdeal ≤ w.asIdeal := by
  let S : Closeds (Spec (.of R)) := ⟨Module.support R M, Module.isClosed_support⟩
  let C := ClosedComponents.components (Spec (.of R)) S
  let F := C.image CycleClass.Thom.IntersectionGeometry.supportPoint
  refine ⟨F, ?_, ?_⟩
  · intro v hv
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hv
    exact ClosedComponents.subset (Spec (.of R)) S B hB
      (B.isIrreducible.isGenericPoint_genericPoint B.isClosed).mem
  · intro w hw
    let D : IrreducibleCloseds (Spec (.of R)) := irreducibleSetEquivPoints.symm w
    have hD : (D : Set (Spec (.of R))) ⊆ S :=
      closure_minimal (Set.singleton_subset_iff.mpr hw) S.isClosed
    obtain ⟨B, hDB⟩ := Supports.closedComponentSupport_covers (Spec (.of R)) S D hD
    let Z := CycleClass.Thom.IntersectionGeometry.closedComponentSupport (Spec (.of R)) S B
    have hZ : Z ∈ C := (ClosedComponents.mem_iff (Spec (.of R)) S Z).mpr ⟨B, rfl⟩
    have hwZ : w ∈ (Z : Set (Spec (.of R))) := hDB (subset_closure (Set.mem_singleton w))
    refine ⟨CycleClass.Thom.IntersectionGeometry.supportPoint Z, Finset.mem_image.mpr ⟨Z, hZ, rfl⟩, ?_⟩
    exact (PrimeSpectrum.le_iff_specializes (CycleClass.Thom.IntersectionGeometry.supportPoint Z) w).mpr
      ((Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).specializes hwZ)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ModuleSupportPrimes
