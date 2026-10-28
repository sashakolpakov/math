import OAI.ArithmeticGeometry.Descent.CMVariety.ConnectedEmbeddedCoefficients

/-! # Group Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.GroupModel

noncomputable section

/-! Spread an actual projective commutative group over any geometric
characteristic-zero field to a connected finite rational coefficient
base, retaining its group law and projective embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

structure GeometricGroupModel (X : Over (Spec (.of k))) [GrpObj X] (n : ℕ) where
  data : PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel ℚ k X n
  group : GrpObj data.toModel.model
  commutative : IsCommMonObj data.toModel.model
  smooth : Smooth data.toModel.model.hom
  proper : IsProper data.toModel.model.hom
  connected : GeometricallyConnected data.toModel.model.hom
  comparison_group :
    letI := group
    letI : GrpObj ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k data.toModel.coefficients)).obj
      data.toModel.model) := Functor.grpObjObj
        (F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k data.toModel.coefficients))
        (G := data.toModel.model)
    IsMonHom data.toModel.genericIso.hom

attribute [instance] GeometricGroupModel.group GeometricGroupModel.commutative
  GeometricGroupModel.smooth GeometricGroupModel.proper GeometricGroupModel.connected
  GeometricGroupModel.comparison_group

theorem exists_geometric_group_model (X : Over (Spec (.of k)))
    [GrpObj X] [IsCommMonObj X] [Smooth X.hom] [IsIntegral X.left]
    (n : ℕ) (embedding : X ⟶ HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace k n)
    [IsClosedImmersion embedding.left] : Nonempty (GeometricGroupModel X n) := by
  obtain ⟨D₀, hs₀, hp₀, hc₀⟩ := ArithmeticGeometry.Descent.CMVariety.ConnectedEmbeddedCoefficients.Abelian.integral_group_has_connected_embedded_coefficient_model
    ℚ k X n embedding
  let M := D₀.toModel.model
  let s := D₀.toModel.coefficients
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k s)
  have : Smooth M.hom := hs₀
  have : IsProper M.hom := hp₀
  have : GeometricallyConnected M.hom := hc₀
  let genericGroup : GrpObj (H.obj M) := GrpObj.ofIso D₀.toModel.genericIso.symm
  have : IsCommMonObj (H.obj M) := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.commutative_group_of_iso D₀.toModel.genericIso.symm
  obtain ⟨t, h, groupN, hcomm, hgroup⟩ := PELModuli.IntegralModel.Coefficient.GroupModels.Coefficients.commutative_group_model_after_enlargement M
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ k h)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k t)
  let Q := F.obj M
  let := groupN
  let : GrpObj (G.obj Q) := Functor.grpObjObj (F := G)
  let c : G.obj Q ≅ H.obj M := (PELModuli.IntegralModel.Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := ℚ) h).app M
  have hc : IsMonHom c.hom := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.image_group_iso_isMonHom G Q (H.obj M) c groupN hgroup
  have he : IsMonHom D₀.toModel.genericIso.hom := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.transported_group_iso_isMonHom D₀.toModel.genericIso
  have : Smooth Q.hom := inferInstanceAs (Smooth (pullback.snd M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ k h)))
  have : IsProper Q.hom := inferInstanceAs (IsProper (pullback.snd M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ k h)))
  let DN : PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel ℚ k X := {
    coefficients := t
    model := Q
    finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
    genericIso := c ≪≫ D₀.toModel.genericIso }
  let DE := ArithmeticGeometry.Descent.CMVariety.EmbeddedCoefficientEnlargement.Abelian.enlargeEmbeddedCoefficientModel D₀ t h
  let D : PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel ℚ k X n := {
    toModel := DN
    embedding := DE.embedding
    closedImmersion := DE.closedImmersion }
  exact ⟨{
    data := D
    group := groupN
    commutative := hcomm
    smooth := inferInstanceAs (Smooth (pullback.snd M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ k h)))
    proper := inferInstanceAs (IsProper (pullback.snd M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ k h)))
    connected := inferInstanceAs (GeometricallyConnected (pullback.snd M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ k h)))
    comparison_group := inferInstanceAs (IsMonHom (c.hom ≫ D₀.toModel.genericIso.hom)) }⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.GroupModel
