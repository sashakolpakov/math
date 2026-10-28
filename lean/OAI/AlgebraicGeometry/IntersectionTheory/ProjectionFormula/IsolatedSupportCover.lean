import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.TorLength

/-! # Isolated Support Cover -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedSupportCover

noncomputable section

/-! Properness against a finite closed support cover forces the
native local module intersection to lie at the closed point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem isolated (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (A : V.DimensionCycleSupport p) (C : V.DimensionCycleSupport (p + q))
    (R : Type) [CommRing R] [IsLocalRing R]
    (u : Spec (.of R) ⟶ V.carrier) (hu : Function.Injective u)
    (hc : u (IsLocalRing.closedPoint R) = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (M N : ModuleCat R) (F : Finset (IrreducibleCloseds V.carrier))
    (hF : ∀ B ∈ F, q ≤ V.supportCodimension B)
    (hproper : ∀ B ∈ F, ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B : Set V.carrier) →
        p + V.supportCodimension B ≤ V.supportCodimension D)
    (hM : ∀ z ∈ Module.support R M, ∃ B ∈ F, u z ∈ (B : Set V.carrier))
    (hN : ∀ z ∈ Module.support R N, u z ∈ (A.val : Set V.carrier)) :
    Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} := by
  intro z hz
  obtain ⟨B, hB, hzB⟩ := hM z hz.1
  let D : IrreducibleCloseds V.carrier := irreducibleSetEquivPoints.symm (u z)
  have hD : (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B : Set V.carrier) :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨hN z hz.2, hzB⟩) (A.val.isClosed.inter B.isClosed)
  have hs : u z ⤳ CycleClass.Thom.IntersectionGeometry.supportPoint C.val := by
    rw [← hc]
    apply Specializes.map _ u.continuous
    exact (PrimeSpectrum.le_iff_specializes z (IsLocalRing.closedPoint R)).mp
      (IsLocalRing.le_maximalIdeal z.isPrime.ne_top)
  have hCD : C.val ≤ D := by
    apply (Supports.supportPoint_mem_iff_subset ⟨D, D.isClosed⟩ C.val).mp
    exact hs.mem_closed isClosed_closure (subset_closure (Set.mem_singleton (u z)))
  have he : C.val = D := by
    by_contra hne
    have hlt := Supports.codimension_strictAnti V m (lt_of_le_of_ne hCD hne)
    have hbound := hproper B hB D hD
    have hdim := hF B hB
    rw [C.property] at hlt
    omega
  have hpoint : u z = CycleClass.Thom.IntersectionGeometry.supportPoint C.val :=
    (irreducibleSetEquivPoints.apply_symm_apply (u z)).symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he.symm)
  exact Set.mem_singleton_iff.mpr (hu (hpoint.trans hc.symm))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedSupportCover
