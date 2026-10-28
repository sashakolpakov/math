import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.SchemeDimension

/-! # Common Closed Carrier Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CommonClosedCarrierData.Construction

noncomputable section

/-! Common integral closed-carrier geometry before any coefficient ideals or programs are introduced. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure DimensionCommonClosedCarrierData (dim : ℕ) {X S : Scheme.{0}} (H H' : X.IdealSheafData) (a b : S ⟶ X) where
  carrier : Scheme.{0}
  integral : IsIntegral carrier
  noetherian : IsLocallyNoetherian carrier
  compact : CompactSpace carrier
  dimension : topologicalKrullDim carrier ≤ dim
  carrierMap : carrier ⟶ S
  left : carrier ⟶ H.subscheme
  right : carrier ⟶ H'.subscheme
  left_etale : Etale left
  right_etale : Etale right
  left_pullback : IsPullback left carrierMap H.subschemeι a
  right_pullback : IsPullback right carrierMap H'.subschemeι b

attribute [instance] DimensionCommonClosedCarrierData.integral DimensionCommonClosedCarrierData.noetherian
  DimensionCommonClosedCarrierData.compact DimensionCommonClosedCarrierData.left_etale DimensionCommonClosedCarrierData.right_etale

theorem exists_dimension_common_closed_carrier_data (dim : ℕ)
    {X S : Scheme.{0}} [IsLocallyNoetherian S] (H H' : X.IdealSheafData)
    (a b : S ⟶ X) [Etale a] [Etale b] (hH : H.comap a = H'.comap b)
    [IsIntegral (H.comap a).subscheme] [CompactSpace (H.comap a).subscheme]
    (hdH : topologicalKrullDim H.subscheme ≤ dim) : Nonempty (DimensionCommonClosedCarrierData dim H H' a b) := by
  let H0 := H.comap a
  let p := IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H H0 a rfl
  let p' := IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H' H0 b hH.symm
  let : IsLocallyNoetherian H0.subscheme := LocallyOfFiniteType.isLocallyNoetherian H0.subschemeι
  exact ⟨{ carrier := H0.subscheme
           integral := inferInstance
           noetherian := inferInstance
           compact := inferInstance
           dimension := Blowups.Etale.SchemeDimension.Construction.scheme_dimension_le_of_etale p dim hdH
           carrierMap := H0.subschemeι
           left := p
           right := p'
           left_etale := inferInstance
           right_etale := inferInstance
           left_pullback := IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_isPullback H H0 a rfl
           right_pullback := IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_isPullback H' H0 b hH.symm }⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CommonClosedCarrierData.Construction
