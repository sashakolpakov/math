import Mathlib.Topology.Sets.Compacts
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Final

/-! # Compact Open Index -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactOpenIndex

noncomputable section

/-!
# Compact supports in an open subspace

Compact subsets of an open subspace are order-equivalent to ambient compact
subsets contained in that open set. The maps are actual subtype image and
preimage. Their compactness follows from the inducing subtype topology; no
separation or local compactness assumption is needed. Consequently every
diagram on these supports has the same colimit after this reindexing.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- View an ambient compact subset contained in `U` as a compact of the
actual subspace `U`, using the inducing subtype topology. -/
def openCompactPreimage (U : Opens X) (K : U.compactsInside) : Compacts U where
  carrier := (Subtype.val : U → X) ⁻¹' (K.val : Set X)
  isCompact' := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    K.val.isCompact (by
      rw [Subtype.range_val]
      exact K.property)

/-- The canonical support-index equivalence: subtype image in one direction,
and subtype preimage in the other. -/
def openCompactsOrderIso (U : Opens X) : Compacts U ≃o U.compactsInside where
  toFun K := ⟨K.map Subtype.val continuous_subtype_val, by
    rintro x ⟨y, _, rfl⟩
    exact y.property⟩
  invFun := openCompactPreimage U
  left_inv K := by
    apply Compacts.ext
    exact Set.preimage_image_eq (K : Set U) Subtype.val_injective
  right_inv K := by
    apply Subtype.ext
    apply Compacts.ext
    apply Set.image_preimage_eq_of_subset
    rw [Subtype.range_val]
    exact K.property
  map_rel_iff' := by
    intro K L
    change (Subtype.val : U → X) '' (K : Set U) ⊆ Subtype.val '' (L : Set U) ↔ K ≤ L
    exact Set.image_subset_image_iff Subtype.val_injective

@[simp]
theorem openCompactsOrderIso_apply_val (U : Opens X) (K : Compacts U) :
    (openCompactsOrderIso U K).val = K.map Subtype.val continuous_subtype_val := rfl

@[simp]
theorem openCompactsOrderIso_symm_coe (U : Opens X) (K : U.compactsInside) :
    ((openCompactsOrderIso U).symm K : Set U) =
      (Subtype.val : U → X) ⁻¹' (K.val : Set X) := rfl

/-- The actual preorder categories of compact supports are equivalent. -/
abbrev openCompactsEquivalence (U : Opens X) : Compacts U ≌ U.compactsInside :=
  (openCompactsOrderIso U).equivalence

variable {C : Type*} [Category* C] (U : Opens X)
  (F : U.compactsInside ⥤ C) [HasColimit F]

/-- Reindexing any genuine compact-support diagram along the subtype-image
equivalence leaves its categorical colimit unchanged. -/
def openCompactsColimitIso :
    colimit ((openCompactsEquivalence U).functor ⋙ F) ≅ colimit F :=
  Functor.Final.colimitIso (openCompactsEquivalence U).functor F

@[reassoc (attr := simp)]
theorem openCompactsColimitIso_ι (K : Compacts U) :
    colimit.ι ((openCompactsEquivalence U).functor ⋙ F) K ≫
        (openCompactsColimitIso U F).hom =
      colimit.ι F (openCompactsOrderIso U K) :=
  Functor.Final.ι_colimitIso_hom (openCompactsEquivalence U).functor F K

@[reassoc (attr := simp)]
theorem openCompactsColimitIso_inv_ι (K : Compacts U) :
    colimit.ι F (openCompactsOrderIso U K) ≫ (openCompactsColimitIso U F).inv =
      colimit.ι ((openCompactsEquivalence U).functor ⋙ F) K :=
  Functor.Final.ι_colimitIso_inv (openCompactsEquivalence U).functor F K

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactOpenIndex
