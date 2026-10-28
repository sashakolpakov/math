import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierBoundaryReindex

/-! # Tangent Carrier Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierData.Construction

noncomputable section

/-! Initial native overlap geometry, independent of any selected resolution program. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure TangentCarrierOverlapData
    {X X' : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J H : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (J' H' : X'.IdealSheafData) (D' : β → X'.IdealSheafData) (n : ℕ) where
  ambient : Scheme
  integral : IsIntegral ambient
  noetherian : IsLocallyNoetherian ambient
  structureMap : ambient ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  smooth : Smooth structureMap
  ideal : ambient.IdealSheafData
  leftCarrier : ambient.IdealSheafData
  rightCarrier : ambient.IdealSheafData
  boundary : β → ambient.IdealSheafData
  left_integral : IsIntegral leftCarrier.subscheme
  right_integral : IsIntegral rightCarrier.subscheme
  left_compact : CompactSpace leftCarrier.subscheme
  right_compact : CompactSpace rightCarrier.subscheme
  left : ambient ⟶ X
  right : ambient ⟶ X'
  left_etale : Etale left
  right_etale : Etale right
  left_ground : left ≫ f = structureMap
  right_ground : right ≫ f' = structureMap
  left_ideal : J.comap left = ideal
  right_ideal : J'.comap right = ideal
  left_carrier : H.comap left = leftCarrier
  right_carrier : H'.comap right = rightCarrier
  left_boundary : ∀ l, (D l).comap left = boundary l
  right_boundary : ∀ l, (D' l).comap right = boundary l
  comparison : letI := smooth
    ∀ x : ambient, x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf structureMap ideal n).support →
      Nonempty (TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt structureMap ideal leftCarrier rightCarrier boundary n x)

attribute [instance] TangentCarrierOverlapData.integral TangentCarrierOverlapData.noetherian
  TangentCarrierOverlapData.smooth TangentCarrierOverlapData.left_integral TangentCarrierOverlapData.right_integral
  TangentCarrierOverlapData.left_compact TangentCarrierOverlapData.right_compact
  TangentCarrierOverlapData.left_etale TangentCarrierOverlapData.right_etale

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierData.Construction
