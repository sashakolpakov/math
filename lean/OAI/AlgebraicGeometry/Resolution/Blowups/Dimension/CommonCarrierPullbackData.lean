import OAI.AlgebraicGeometry.Resolution.Blowups.CommonCarrierCoefficientEquality
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.SchemeDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PullbackCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CommonClosedCarrierData

/-! # Common Carrier Pullback Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CommonCarrierPullbackData.Construction

noncomputable section

/-! Geometric data for the common carrier, independent of recursive program certificates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure DimensionCommonCarrierPullbackData (dim : ℕ)
    {X S : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (H H' : X.IdealSheafData)
    (C : H.subscheme.IdealSheafData) (C' : H'.subscheme.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (a b : S ⟶ X) where
  carrier : Scheme
  integral : IsIntegral carrier
  noetherian : IsLocallyNoetherian carrier
  compact : CompactSpace carrier
  dimension : topologicalKrullDim carrier ≤ dim
  structureMap : carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  carrierMap : carrier ⟶ S
  left : carrier ⟶ H.subscheme
  right : carrier ⟶ H'.subscheme
  left_etale : Etale left
  right_etale : Etale right
  left_structure : left ≫ (H.subschemeι ≫ f) = structureMap
  right_structure : right ≫ (H'.subschemeι ≫ f) = structureMap
  ideal : carrier.IdealSheafData
  ideal_ne_bot : ideal ≠ ⊥
  left_ideal : C.comap left = ideal
  right_ideal : C'.comap right = ideal
  boundary : β → carrier.IdealSheafData
  left_boundary : ∀ l, ((D l).comap H.subschemeι).comap left = boundary l
  right_boundary : ∀ l, ((D l).comap H'.subschemeι).comap right = boundary l
  left_pullback : IsPullback left carrierMap H.subschemeι a
  right_pullback : IsPullback right carrierMap H'.subschemeι b

attribute [instance] DimensionCommonCarrierPullbackData.integral DimensionCommonCarrierPullbackData.noetherian
  DimensionCommonCarrierPullbackData.compact DimensionCommonCarrierPullbackData.left_etale DimensionCommonCarrierPullbackData.right_etale

theorem exists_dimension_common_carrier_pullback_data (dim : ℕ)
    {X S : Scheme} [IsLocallyNoetherian S] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J H H' : X.IdealSheafData) [IsIntegral H.subscheme]
    (C : H.subscheme.IdealSheafData) (C' : H'.subscheme.IdealSheafData)
    (d : ℕ) (hC : C ≠ ⊥) (hCdef : C = GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J d H.subschemeι)
    (hC'def : C' = GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J d H'.subschemeι)
    {β : Type} (D : β → X.IdealSheafData) (a b : S ⟶ X) [Etale a] [Etale b]
    (hf : a ≫ f = b ≫ f) (hJ : J.comap a = J.comap b) (hH : H.comap a = H'.comap b)
    (hD : ∀ l, (D l).comap a = (D l).comap b)
    [IsIntegral (H.comap a).subscheme] [CompactSpace (H.comap a).subscheme]
    (hdH : topologicalKrullDim H.subscheme ≤ dim) :
    Nonempty (DimensionCommonCarrierPullbackData dim f H H' C C' D a b) := by
  obtain ⟨A⟩ := CommonClosedCarrierData.Construction.exists_dimension_common_closed_carrier_data dim H H' a b hH hdH
  have heC : C.comap A.left = C'.comap A.right := by
    rw [hCdef, hC'def]
    exact CommonCarrierCoefficientEquality.Construction.smoothCoefficientIdealSheaf_common_carrier f J d H.subschemeι H'.subschemeι A.carrierMap
      a b A.left A.right A.left_pullback.w A.right_pullback.w hf hJ
  have heD (l : β) : ((D l).comap H.subschemeι).comap A.left = ((D l).comap H'.subschemeι).comap A.right :=
    CommonCarrierCoefficientEquality.Construction.idealSheaf_common_carrier_pullback (D l) H.subschemeι H'.subschemeι A.carrierMap a b A.left A.right
      A.left_pullback.w A.right_pullback.w (hD l)
  refine ⟨{ carrier := A.carrier
            integral := inferInstance
            noetherian := inferInstance
            compact := inferInstance
            dimension := A.dimension
            structureMap := A.carrierMap ≫ (a ≫ f)
            carrierMap := A.carrierMap
            left := A.left
            right := A.right
            left_etale := inferInstance
            right_etale := inferInstance
            left_structure := ?_
            right_structure := ?_
            ideal := C.comap A.left
            ideal_ne_bot := Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_nonempty_etale_ne_bot A.left C hC
            left_ideal := rfl
            right_ideal := heC.symm
            boundary := fun l => ((D l).comap H.subschemeι).comap A.left
            left_boundary := fun _ => rfl
            right_boundary := fun l => (heD l).symm
            left_pullback := A.left_pullback
            right_pullback := A.right_pullback }⟩
  · rw [← Category.assoc, A.left_pullback.w, Category.assoc]
  · rw [← Category.assoc, A.right_pullback.w, Category.assoc, hf]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CommonCarrierPullbackData.Construction
