import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrimeCodimension

/-! # Support Representative -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportRepresentative

noncomputable section

/-! Every global support containing a chart point has a unique
generic affine prime specializing to that point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem exists_prime {R : Type} [CommRing R] {X : Scheme}
    (j : Spec (.of R) ⟶ X) [IsOpenImmersion j]
    (B : IrreducibleCloseds X) (x : PrimeSpectrum R) (hx : j x ∈ (B : Set X)) :
    ∃ z : PrimeSpectrum R, j z = CycleClass.Thom.IntersectionGeometry.supportPoint B ∧ FiltrationAvoidance.support j z = B ∧ z.asIdeal ≤ x.asIdeal := by
  have hs : CycleClass.Thom.IntersectionGeometry.supportPoint B ⤳ j x :=
    (B.isIrreducible.isGenericPoint_genericPoint B.isClosed).specializes hx
  have hr : CycleClass.Thom.IntersectionGeometry.supportPoint B ∈ j.opensRange := hs.mem_open j.opensRange.isOpen ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hr
  refine ⟨z, hz, ?_, ?_⟩
  · exact (congrArg irreducibleSetEquivPoints.symm hz).trans
      (irreducibleSetEquivPoints.symm_apply_apply B)
  · apply (PrimeSpectrum.le_iff_specializes z x).mpr
    apply j.isOpenEmbedding.isInducing.specializes_iff.mp
    exact hz.symm ▸ hs

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportRepresentative
