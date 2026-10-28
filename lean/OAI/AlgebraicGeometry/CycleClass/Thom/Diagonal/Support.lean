import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport

/-! # Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions

noncomputable section

/-! Original irreducible supports on the diagonal and their exact
codimensions. Algebraic codimension bounds transfer to the actual
diagonal intersection in the smooth projective product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)

local notation "T" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.productVariety V V
local notation "δ" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonal V

local instance : IsIntegral (Ambient.Constructions.productVariety V V).carrier := (Ambient.Constructions.productVariety V V).property

def diagonalClosedSupport : IrreducibleCloseds (T).carrier := Geometric.StratumClosure.integralImageClosure (Ambient.Constructions.diagonal V).left

theorem diagonalClosedSupport_coe : (diagonalClosedSupport V : Set (T).carrier) = Set.range (δ).left :=
  (δ).left.isClosedEmbedding.isClosed_range.closure_eq

theorem exists_diagonal_source (D : IrreducibleCloseds (T).carrier)
    (hD : (D : Set (T).carrier) ⊆ Set.range (δ).left) :
    ∃ A : IrreducibleCloseds V.carrier, Scheme.ProperSupport.Constructions.imageSupport δ A = D := by
  obtain ⟨x, hx⟩ := hD (D.isIrreducible.isGenericPoint_genericPoint D.isClosed).mem
  let A : IrreducibleCloseds V.carrier := irreducibleSetEquivPoints.symm x
  refine ⟨A, irreducibleSetEquivPoints.injective ?_⟩
  rw [Scheme.ProperSupport.Constructions.imageSupport_genericPoint]
  exact (congrArg (δ).left (irreducibleSetEquivPoints.apply_symm_apply x)).trans hx

theorem diagonal_image_dimension (A : IrreducibleCloseds V.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Scheme.ProperSupport.Constructions.imageSupport δ A) (T).structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension A V.structureMap := by
  let : IsClosedImmersion (ProperImage.SupportMap.Constructions.Construction.algebraicMap δ) := Ambient.Constructions.diagonal_closed V
  have h := Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure
    (Geometric.GenericPoint.reducedSupportι A ≫ ProperImage.SupportMap.Constructions.Construction.algebraicMap δ) (T).structureMap
  rw [Category.assoc, ProperImage.SupportMap.Constructions.Construction.algebraicMap_over] at h
  exact h.symm

theorem diagonal_image_codimension (A : IrreducibleCloseds V.carrier) :
    Geometric.DimensionCycles.dimensionCodimension T (Scheme.ProperSupport.Constructions.imageSupport δ A) =
      Geometric.DimensionCycles.dimensionCodimension V A + V.complexDimension := by
  have hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (T).structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap + Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
    simpa only [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension] using Ambient.Constructions.product_dimension V V
  have hA := Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le A V.structureMap
  unfold Geometric.DimensionCycles.dimensionCodimension
  rw [diagonal_image_dimension, hdim, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension]
  omega

theorem diagonal_image_dimension_bound (F : Set V.carrier) (d : ℕ)
    (hF : ∀ A : IrreducibleCloseds V.carrier, (A : Set V.carrier) ⊆ F → d ≤ Geometric.DimensionCycles.dimensionCodimension V A)
    (D : IrreducibleCloseds (T).carrier) (hD : (D : Set (T).carrier) ⊆ (δ).left '' F) :
    d + V.complexDimension ≤ Geometric.DimensionCycles.dimensionCodimension T D := by
  obtain ⟨A, hA⟩ := exists_diagonal_source V D (hD.trans (Set.image_subset_range _ _))
  have hAF : (A : Set V.carrier) ⊆ F := by
    intro x hx
    have hxD : (δ).left x ∈ (D : Set (T).carrier) := by
      rw [← hA, Scheme.ProperSupport.Constructions.imageSupport_eq_image]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hD hxD
    exact (δ).left.isClosedEmbedding.injective he ▸ hy
  rw [← hA, diagonal_image_codimension]
  exact Nat.add_le_add_right (hF A hAF) _

theorem diagonal_product_intersection (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) :
    (diagonalClosedSupport V : Set (T).carrier) ∩
      ((Integral.ProductSupport.Constructions.integralProductSupport V V T (Ambient.Constructions.first V V) (Ambient.Constructions.second V V) (Ambient.Constructions.productLimit V V) p q A B).val : Set (T).carrier) =
        (δ).left '' ((A.val : Set V.carrier) ∩ (B.val : Set V.carrier)) := by
  rw [diagonalClosedSupport_coe, ← Ambient.Constructions.diagonal_product_preimage V p q A B]
  exact (Set.inter_comm _ _).trans Set.image_preimage_eq_inter_range.symm

theorem diagonal_product_dimension_bound (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
    (hproper : ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V D)
    (D : IrreducibleCloseds (T).carrier)
    (hD : (D : Set (T).carrier) ⊆ (diagonalClosedSupport V : Set (T).carrier) ∩
      ((Integral.ProductSupport.Constructions.integralProductSupport V V T (Ambient.Constructions.first V V) (Ambient.Constructions.second V V) (Ambient.Constructions.productLimit V V) p q A B).val : Set (T).carrier)) :
    (p + q) + V.complexDimension ≤ Geometric.DimensionCycles.dimensionCodimension T D := by
  rw [diagonal_product_intersection] at hD
  exact diagonal_image_dimension_bound V _ (p + q) hproper D hD

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions
