import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Reduced Closed -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed

noncomputable section

/-!
# Reduced induced schemes on arbitrary closed subsets

This is the reduced induced scheme construction without an irreducibility
hypothesis. The vanishing ideal is genuinely radical on affine opens, and the
resulting closed immersion has precisely the requested underlying image.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The radical ideal sheaf vanishing on the specified closed subset. -/
def reducedClosedIdeal (Z : Closeds X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal Z

/-- The reduced induced scheme on an arbitrary closed subset. -/
def reducedClosedScheme (Z : Closeds X) : Scheme.{u} :=
  (reducedClosedIdeal Z).subscheme

/-- The canonical inclusion of the reduced closed subscheme. -/
def reducedClosedι (Z : Closeds X) : reducedClosedScheme Z ⟶ X :=
  (reducedClosedIdeal Z).subschemeι

instance reducedClosedι_isClosedImmersion (Z : Closeds X) :
    IsClosedImmersion (reducedClosedι Z) :=
  inferInstanceAs (IsClosedImmersion (reducedClosedIdeal Z).subschemeι)

@[simp]
theorem range_reducedClosedι (Z : Closeds X) :
    Set.range (reducedClosedι Z) = (Z : Set X) := by
  change Set.range (reducedClosedIdeal Z).subschemeι = (Z : Set X)
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [reducedClosedIdeal]

/-- The canonical inclusion is a genuine topological closed embedding. -/
theorem reducedClosedι_isClosedEmbedding (Z : Closeds X) :
    Topology.IsClosedEmbedding (reducedClosedι Z) :=
  (reducedClosedι Z).isClosedEmbedding

instance reducedClosedScheme_isReduced (Z : Closeds X) :
    AlgebraicGeometry.IsReduced (reducedClosedScheme Z) := by
  let I := reducedClosedIdeal Z
  change AlgebraicGeometry.IsReduced I.subscheme
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).2
  intro U
  change X.affineOpens at U
  change AlgebraicGeometry.IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
  apply (AlgebraicGeometry.affine_isReduced_iff _).2
  apply (Ideal.isRadical_iff_quotient_reduced _).1
  change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- Nonemptiness of the prescribed closed set gives a point of its induced scheme. -/
theorem reducedClosedScheme_nonempty (Z : Closeds X) (hZ : (Z : Set X).Nonempty) :
    Nonempty (reducedClosedScheme Z) := by
  obtain ⟨x, hx⟩ := hZ
  have h : x ∈ Set.range (reducedClosedι Z) := by
    rw [range_reducedClosedι]
    exact hx
  obtain ⟨y, _⟩ := h
  exact ⟨y⟩

/-- The induced structure morphism is the original one composed with inclusion. -/
def reducedClosedStructureMap (Z : Closeds X) {S : Scheme.{u}} (f : X ⟶ S) :
    reducedClosedScheme Z ⟶ S :=
  reducedClosedι Z ≫ f

@[simp]
theorem reducedClosedStructureMap_eq (Z : Closeds X) {S : Scheme.{u}} (f : X ⟶ S) :
    reducedClosedStructureMap Z f = reducedClosedι Z ≫ f := rfl

instance reducedClosedStructureMap_locallyOfFiniteType (Z : Closeds X)
    {S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (reducedClosedStructureMap Z f) := by
  dsimp [reducedClosedStructureMap]
  infer_instance

instance reducedClosedStructureMap_locallyOfFinitePresentation (Z : Closeds X)
    {S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (reducedClosedStructureMap Z f) :=
  inferInstance

instance reducedClosedScheme_isLocallyNoetherian [IsLocallyNoetherian X] (Z : Closeds X) :
    IsLocallyNoetherian (reducedClosedScheme Z) :=
  LocallyOfFiniteType.isLocallyNoetherian (reducedClosedι Z)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed
