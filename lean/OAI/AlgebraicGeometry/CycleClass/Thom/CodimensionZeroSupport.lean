import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectiveComponentDimension

/-! # Codimension Zero Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CodimensionZeroSupport

noncomputable section

/-! A support of codimension zero is its actual integral component.
The reduced support scheme is canonically isomorphic to that component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

theorem integralSupport_eq_univ_of_codimension_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (W : IrreducibleCloseds V.carrier) (hW : Geometric.DimensionCycles.dimensionCodimension V W = 0) :
    (W : Set V.carrier) = Set.univ := by
  let T : IrreducibleCloseds V.carrier :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ V.carrier, isClosed_univ⟩
  have hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension W V.structureMap :=
    Nat.sub_eq_zero_iff_le.mp hW
  by_contra hne
  have hlt : W < T := lt_of_le_of_ne (Set.subset_univ _) (fun he => hne (congrArg SetLike.coe he))
  have h := (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt W T V.structureMap hlt).trans_le
    (Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le T V.structureMap)
  exact (not_lt_of_ge hd) h

theorem support_eq_component_of_codimension_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier) (hW : X.supportCodimension W = 0) :
    (W : Set X.carrier) = (X.supportComponent W).val := by
  let C := X.supportComponent W
  let B := X.componentSupportPreimage C W (X.support_subset_component W)
  have hB : Geometric.DimensionCycles.dimensionCodimension (X.componentVariety C) B = 0 := by
    rw [← X.supportCodimension_componentSupportImage C B,
      X.componentSupportImage_preimage C W (X.support_subset_component W)]
    exact hW
  have hu := integralSupport_eq_univ_of_codimension_zero (X.componentVariety C) B hB
  have he := congrArg (fun A : IrreducibleCloseds X.carrier => (A : Set X.carrier))
    (X.componentSupportImage_preimage C W (X.support_subset_component W))
  change X.componentInclusion C '' (B : Set (X.componentVariety C).carrier) = (W : Set X.carrier) at he
  rw [hu, Set.image_univ, X.componentInclusion_range C] at he
  exact he.symm

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)
  (hW : X.supportCodimension W = 0)

include hW in
theorem componentInclusion_imageClosure :
    Geometric.StratumClosure.integralImageClosure (X.componentInclusion (X.supportComponent W)) = W := by
  apply IrreducibleCloseds.ext
  change closure (Set.range (X.componentInclusion (X.supportComponent W))) = (W : Set X.carrier)
  rw [X.componentInclusion_range, ← support_eq_component_of_codimension_zero X W hW, W.isClosed.closure_eq]

/-- The actual scheme isomorphism preserves the closed inclusion into the ambient scheme. -/
def componentReducedSupportIso : (X.componentVariety (X.supportComponent W)).carrier ≅ Geometric.GenericPoint.reducedSupportScheme W := by
  have hk : (Geometric.GenericPoint.reducedSupportι W).ker = (X.componentInclusion (X.supportComponent W)).ker := by
    rw [Geometric.StratumClosure.kernel_eq_reducedImageClosureIdeal (X.componentInclusion (X.supportComponent W)),
      componentInclusion_imageClosure X W hW]
    exact Scheme.IdealSheafData.ker_subschemeι (Geometric.GenericPoint.reducedSupportIdeal W)
  let f := IsClosedImmersion.lift (Geometric.GenericPoint.reducedSupportι W) (X.componentInclusion (X.supportComponent W)) hk.le
  let : IsIso f := IsClosedImmersion.isIso_lift
    (Geometric.GenericPoint.reducedSupportι W) (X.componentInclusion (X.supportComponent W)) hk
  exact asIso f

theorem componentReducedSupportIso_inclusion :
    (componentReducedSupportIso X W hW).hom ≫ Geometric.GenericPoint.reducedSupportι W =
      X.componentInclusion (X.supportComponent W) := by
  change IsClosedImmersion.lift _ _ _ ≫ _ = _
  exact IsClosedImmersion.lift_fac _ _ _

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CodimensionZeroSupport
