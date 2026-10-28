import OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps

/-! # Homology Boundary Equality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.HomologyBoundaryEquality.ModuleHomologyBoundaryEquality

noncomputable section

/-! Two actual maps of module short complexes agree on homology when
their values on every cycle differ by a boundary. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps
universe u v
variable {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{v} R)} (f g : S ⟶ T)
  (h : ∀ x : S.X₂, S.g x = 0 → ∃ b : T.X₁, f.τ₂ x - g.τ₂ x = T.f b)

include h in
theorem quotient : PeriodInvariants.ModuleHomologyMaps.quotientMap f = PeriodInvariants.ModuleHomologyMaps.quotientMap g := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective q
  obtain ⟨b, hb⟩ := h x.val x.property
  change (Submodule.Quotient.mk (PeriodInvariants.ModuleHomologyMaps.cycleMap f x) :
    LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) = Submodule.Quotient.mk (PeriodInvariants.ModuleHomologyMaps.cycleMap g x)
  exact (Submodule.Quotient.eq _).mpr ⟨b, Subtype.ext hb.symm⟩

include h in
theorem homology : ShortComplex.homologyMap f = ShortComplex.homologyMap g := by
  apply (cancel_mono T.moduleCatHomologyIso.hom).mp
  rw [PeriodInvariants.ModuleHomologyMaps.homologyMap_natural, PeriodInvariants.ModuleHomologyMaps.homologyMap_natural, quotient f g h]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.HomologyBoundaryEquality.ModuleHomologyBoundaryEquality
