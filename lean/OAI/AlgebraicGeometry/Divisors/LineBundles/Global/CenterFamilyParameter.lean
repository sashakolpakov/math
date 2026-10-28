import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.CenterFamilyBetti

/-! # Center Family Parameter -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterFamilyParameter.BundleCycles

noncomputable section

/-! The global center family preserves the actual deformation parameter;
its algebraic constant sections therefore lie over exactly zero and one. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem globalCenterDeformationLineIso_inv_coordinate {X : Scheme.{0}} (I : X.IdealSheafData) :
    (CenterDeformationIso.BundleCycles.globalCenterDeformationLineIso I).inv.appTop (Support.Specialization.BundleCycles.globalSupportParameterSection I I) =
      AffineLine.Space.BundleCycles.affineLineCoordinate I.subscheme := by
  rw [← CenterDeformation.BundleCycles.globalCenterDeformationToLine_coordinate]
  change ((CenterDeformationIso.BundleCycles.globalCenterDeformationLineIso I).inv ≫ (CenterDeformationIso.BundleCycles.globalCenterDeformationLineIso I).hom).appTop
    (AffineLine.Space.BundleCycles.affineLineCoordinate I.subscheme) = _
  rw [Iso.inv_hom_id, Scheme.Hom.id_appTop]
  rfl

theorem globalCenterFamily_parameter {X : Scheme.{0}} (I : X.IdealSheafData) :
    (CenterDeformationIso.BundleCycles.globalCenterFamily I).appTop (Specialization.BundleCycles.globalDeformationParameterSection I) = AffineLine.Space.BundleCycles.affineLineCoordinate I.subscheme := by
  change (CenterDeformationIso.BundleCycles.globalCenterDeformationLineIso I).inv.appTop (Support.Specialization.BundleCycles.globalSupportParameterSection I I) = _
  exact globalCenterDeformationLineIso_inv_coordinate I

theorem graphCenterFamily_parameter {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) :
    (CenterDeformationIso.BundleCycles.graphCenterFamily f).appTop (Specialization.BundleCycles.globalDeformationParameterSection (Graph.OpenAmbient.BundleCycles.graph f).ker) =
      AffineLine.Space.BundleCycles.affineLineCoordinate X.carrier := by
  change (AffineSpace.map PUnit (Graph.OpenAmbient.BundleCycles.graph f).toImage).appTop
    ((CenterDeformationIso.BundleCycles.globalCenterFamily (Graph.OpenAmbient.BundleCycles.graph f).ker).appTop (Specialization.BundleCycles.globalDeformationParameterSection (Graph.OpenAmbient.BundleCycles.graph f).ker)) = _
  rw [globalCenterFamily_parameter]
  exact AffineSpace.map_appTop_coord (Graph.OpenAmbient.BundleCycles.graph f).toImage PUnit.unit

theorem graphCenterFamilyEndpoint_parameter {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (a : ℂ) :
    (Graph.CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint f a).left.appTop (Specialization.BundleCycles.globalDeformationParameterSection (Graph.OpenAmbient.BundleCycles.graph f).ker) =
      AffineLine.ConstantSections.BundleCycles.complexScalarSection X.toOver a := by
  change (AffineLine.ConstantSections.BundleCycles.affineLineConstantSection X.toOver a).appTop
    ((CenterDeformationIso.BundleCycles.graphCenterFamily f).appTop (Specialization.BundleCycles.globalDeformationParameterSection (Graph.OpenAmbient.BundleCycles.graph f).ker)) = _
  rw [graphCenterFamily_parameter]
  exact AffineLine.ConstantSections.BundleCycles.affineLineConstantSection_coordinate X.toOver a

theorem graphCenterFamilyEndpoint_zero_parameter {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) :
    (Graph.CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint f 0).left.appTop (Specialization.BundleCycles.globalDeformationParameterSection (Graph.OpenAmbient.BundleCycles.graph f).ker) = 0 := by
  rw [graphCenterFamilyEndpoint_parameter]
  change X.structureMap.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv 0) = 0
  rw [map_zero, map_zero]

theorem graphCenterFamilyEndpoint_one_parameter {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) :
    (Graph.CenterFamilyBetti.BundleCycles.graphCenterFamilyEndpoint f 1).left.appTop (Specialization.BundleCycles.globalDeformationParameterSection (Graph.OpenAmbient.BundleCycles.graph f).ker) = 1 := by
  rw [graphCenterFamilyEndpoint_parameter]
  change X.structureMap.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv 1) = 1
  rw [map_one, map_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterFamilyParameter.BundleCycles
