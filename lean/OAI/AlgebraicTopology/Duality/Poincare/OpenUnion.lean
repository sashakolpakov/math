import OAI.AlgebraicTopology.Duality.Poincare.Property
import OAI.AlgebraicTopology.Duality.Poincare.NestedOpenCapNaturality
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpenUnion

/-! # Open Union -/

namespace OAI.AlgebraicTopology.Duality.Poincare

noncomputable section

/-!
# Canonical Poincare duality and increasing open unions

The genuine canonical cap transformation commutes with the proved colimit
comparisons for compact-support cohomology and rational singular homology.
Consequently canonical cap isomorphisms on the members of an increasing
open sequence imply the canonical cap isomorphism on its union. Actual
compact-support cohomology vanishing passes to the union as well.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Vanishing

variable {X : TopCat.{0}} [T2Space X]

/-- Actual compact-support cohomology vanishing is preserved by an increasing open union. -/
theorem OpenUnion.compactSupportIncreasingUnion_isZero
    (U : ℕ → Opens X) (hU : Monotone U) (n : ℕ)
    (hzero : ∀ i, IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (U i)) n)) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (⨆ i, U i : Opens X)) n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine subsingleton_of_forall_eq 0 ?_
  intro c
  obtain ⟨i, a, ha⟩ := CompactSupportOpenUnion.compactSupportIncreasingUnion_exists_stage U hU n c
  rw [← ha]
  have ha0 : a = 0 := @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (hzero i)) a 0
  simp only [ha0, map_zero]

/-- Actual compact-support cohomology vanishing on an increasing cover implies ambient vanishing. -/
theorem OpenUnion.compactSupportIncreasingAmbient_isZero
    (U : ℕ → Opens X) (hU : Monotone U) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ)
    (hzero : ∀ i, IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (U i)) n)) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine subsingleton_of_forall_eq 0 ?_
  intro c
  obtain ⟨i, a, ha⟩ := CompactSupportOpenUnion.compactSupportIncreasingAmbient_exists_stage U hU hcover n c
  rw [← ha]
  have ha0 : a = 0 := @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (hzero i)) a 0
  simp only [ha0, map_zero]

end Vanishing

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The colimit of the actual stage cap maps agrees with canonical cap on the union. -/
@[reassoc]
theorem OpenUnion.complexManifoldCompactSupportCap_increasingUnion_comparison
    (U : ℕ → Opens M) (hU : Monotone U) (p q : ℕ) (hpq : p + q = 2 * d) :
    (CompactSupportOpenUnion.compactSupportIncreasingOpenUnionIso (X := TopCat.of M) U hU p).hom ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap d (M := (⨆ i, U i : Opens M)) p q hpq =
      colimMap (NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq) ≫
        (RationalSingularOpenUnion.rationalOpenUnionHomologyColimitIso (X := TopCat.of M) U hU q).hom := by
  apply colimit.hom_ext (F := CompactSupportOpenUnion.compactSupportIncreasingOpenDiagram (X := TopCat.of M) U hU p)
  intro i
  rw [CompactSupportOpenUnion.compactSupportIncreasingOpenUnionIso_ι_assoc, ι_colimMap_assoc,
    RationalSingularOpenUnion.rationalOpenUnionHomologyColimitIso_ι]
  exact NestedOpenCapNaturality.complexManifoldCompactSupportCap_opensInclusion d (U i) (⨆ j, U j)
    (le_iSup U i) p q hpq

/-- For a full increasing cover, the same comparison is the actual ambient canonical cap. -/
@[reassoc]
theorem OpenUnion.complexManifoldCompactSupportCap_increasingCover_comparison
    (U : ℕ → Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (CompactSupportOpenUnion.compactSupportIncreasingOpenAmbientIso (X := TopCat.of M) U hU hcover p).hom ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq =
      colimMap (NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq) ≫
        (RationalSingularOpenUnion.rationalIncreasingOpenHomologyAmbientIso (X := TopCat.of M) U hU hcover q).hom := by
  apply colimit.hom_ext (F := CompactSupportOpenUnion.compactSupportIncreasingOpenDiagram (X := TopCat.of M) U hU p)
  intro i
  rw [CompactSupportOpenUnion.compactSupportIncreasingOpenAmbientIso_ι_assoc, ι_colimMap_assoc,
    RationalSingularOpenUnion.rationalIncreasingOpenHomologyAmbientIso_ι]
  exact CanonicalCapNaturality.complexManifoldCompactSupportCap_open d (U i) p q hpq

/-- If the actual canonical cap maps are isomorphisms at each open stage,
the canonical cap map on the increasing union is an isomorphism. -/
theorem OpenUnion.complexManifoldCompactSupportCap_iSup_isIso
    (U : ℕ → Opens M) (hU : Monotone U) (p q : ℕ) (hpq : p + q = 2 * d)
    (hcap : ∀ i, IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U i) p q hpq)) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := (⨆ i, U i : Opens M)) p q hpq) := by
  have : ∀ i, IsIso
      ((NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq).app i) := hcap
  have : IsIso (NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (colimMap (NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq)) := by
    change IsIso ((colim : (ℕ ⥤ ModuleCat.{0} ℚ) ⥤ ModuleCat.{0} ℚ).map _)
    infer_instance
  have heq : ComplexManifoldCap.complexManifoldCompactSupportCap d (M := (⨆ i, U i : Opens M)) p q hpq =
      (CompactSupportOpenUnion.compactSupportIncreasingOpenUnionIso (X := TopCat.of M) U hU p).inv ≫
        colimMap (NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq) ≫
          (RationalSingularOpenUnion.rationalOpenUnionHomologyColimitIso (X := TopCat.of M) U hU q).hom := by
    apply (cancel_epi (CompactSupportOpenUnion.compactSupportIncreasingOpenUnionIso
      (X := TopCat.of M) U hU p).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact OpenUnion.complexManifoldCompactSupportCap_increasingUnion_comparison d U hU p q hpq
  rw [heq]
  infer_instance

/-- Canonical cap duality also passes from an increasing open cover to the actual ambient manifold. -/
theorem OpenUnion.complexManifoldCompactSupportCap_of_increasingCover_isIso
    (U : ℕ → Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (p q : ℕ) (hpq : p + q = 2 * d)
    (hcap : ∀ i, IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U i) p q hpq)) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq) := by
  have : ∀ i, IsIso
      ((NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq).app i) := hcap
  have : IsIso (NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (colimMap (NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq)) := by
    change IsIso ((colim : (ℕ ⥤ ModuleCat.{0} ℚ) ⥤ ModuleCat.{0} ℚ).map _)
    infer_instance
  have heq : ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq =
      (CompactSupportOpenUnion.compactSupportIncreasingOpenAmbientIso (X := TopCat.of M) U hU hcover p).inv ≫
        colimMap (NestedOpenCapNaturality.complexManifoldIncreasingOpenCapNat d (M := M) U hU p q hpq) ≫
          (RationalSingularOpenUnion.rationalIncreasingOpenHomologyAmbientIso (X := TopCat.of M) U hU hcover q).hom := by
    apply (cancel_epi (CompactSupportOpenUnion.compactSupportIncreasingOpenAmbientIso
      (X := TopCat.of M) U hU hcover p).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact OpenUnion.complexManifoldCompactSupportCap_increasingCover_comparison d U hU hcover p q hpq
  rw [heq]
  infer_instance

/-- The full transparent canonical Poincare property is preserved under increasing open unions. -/
theorem Property.HasCanonicalPoincareDuality.iSup
    (U : ℕ → Opens M) (hU : Monotone U)
    (hPD : ∀ i, Property.HasCanonicalPoincareDuality d (U i)) :
    Property.HasCanonicalPoincareDuality d (⨆ i, U i : Opens M) := by
  constructor
  · intro p q hpq
    exact OpenUnion.complexManifoldCompactSupportCap_iSup_isIso d U hU p q hpq
      (fun i => (hPD i).cap_isIso p q hpq)
  · intro p hp
    exact OpenUnion.compactSupportIncreasingUnion_isZero (X := TopCat.of M) U hU p
      (fun i => (hPD i).cohomology_isZero p hp)

/-- The same full property holds on a manifold admitting an increasing open cover with that property. -/
theorem Property.HasCanonicalPoincareDuality.of_increasingOpenCover
    (U : ℕ → Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hPD : ∀ i, Property.HasCanonicalPoincareDuality d (U i)) :
    Property.HasCanonicalPoincareDuality d M := by
  constructor
  · intro p q hpq
    exact OpenUnion.complexManifoldCompactSupportCap_of_increasingCover_isIso d U hU hcover p q hpq
      (fun i => (hPD i).cap_isIso p q hpq)
  · intro p hp
    exact OpenUnion.compactSupportIncreasingAmbient_isZero (X := TopCat.of M) U hU hcover p
      (fun i => (hPD i).cohomology_isZero p hp)

end

end OAI.AlgebraicTopology.Duality.Poincare
