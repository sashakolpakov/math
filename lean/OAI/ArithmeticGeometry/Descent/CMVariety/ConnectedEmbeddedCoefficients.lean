import OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedGoodOpenModels
import OAI.ArithmeticGeometry.Descent.CMVariety.GroupConnectedSpread
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Connected Embedded Coefficients -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ConnectedEmbeddedCoefficients.Abelian

noncomputable section

section

/-! Construct geometrically connected smooth proper embedded coefficient
models of integral smooth commutative groups over an algebraically closed
characteristic-zero field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem integral_group_has_connected_embedded_coefficient_model
    (R K : Type) [CommRing R] [IsNoetherianRing R] [Field K] [IsAlgClosed K]
    [CharZero K] [Algebra R K]
    (X : Over (Spec (.of K))) [GrpObj X] [IsCommMonObj X] [Smooth X.hom] [IsIntegral X.left]
    (n : ℕ) (embedding : X ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n) [IsClosedImmersion embedding.left] :
    ∃ D : AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel R K X n,
      Smooth D.toModel.model.hom ∧ IsProper D.toModel.model.hom ∧
      GeometricallyConnected D.toModel.model.hom := by
  obtain ⟨D₀, hs₀, hp₀⟩ := AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.smooth_projective_coefficient_model R K X n embedding
  have : Smooth D₀.toModel.model.hom := hs₀
  have : IsProper D₀.toModel.model.hom := hp₀
  obtain ⟨W, f, MW, hW, hf, _, hconnW, hirrW⟩ :=
    GoodOpenCoefficientModels.Abelian.smooth_integral_has_good_open_coefficient_model R K X
  have : IsAffine W.left := hW
  have : IsOpenImmersion f.left := hf
  have : GeometricallyConnected MW.model.hom := hconnW
  have : GeometricallyIrreducible MW.model.hom := hirrW
  obtain ⟨D, V, i, hconnV, _, hi, hsD, hpD⟩ :=
    EmbeddedGoodOpenModels.Abelian.embedded_model_has_good_open_after_enlargement f MW D₀
  let M := D.toModel.model
  have : Smooth M.hom := hsD
  have : IsProper M.hom := hpD
  have : GeometricallyConnected V.hom := hconnV
  have : IsOpenImmersion i.left := hi
  let H := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K D.toModel.coefficients)
  let genericGroup : GrpObj (H.obj M) := GrpObj.ofIso D.toModel.genericIso.symm
  have : IsCommMonObj (H.obj M) := Models.SpreadingOut.GroupReflection.Construction.commutative_group_of_iso D.toModel.genericIso.symm
  obtain ⟨t, h, groupN, _, _⟩ := AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GroupModels.Coefficients.commutative_group_model_after_enlargement M
  let F := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  let D₁ := EmbeddedCoefficientEnlargement.Abelian.enlargeEmbeddedCoefficientModel D t h
  let M₁ := D₁.toModel.model
  let groupM₁ : GrpObj M₁ := groupN
  have hsm₁ : Smooth M₁.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_smooth D.toModel t h
  have hproper₁ : IsProper M₁.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_proper D.toModel t h
  have hconn₁ : GeometricallyConnected (F.obj V).hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd V.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)))
  have hopen₁ : IsOpenImmersion (F.map i).left := MorphismProperty.overPullbackMap
    (P := @IsOpenImmersion) (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) i hi
  have : IsIso D₁.toModel.genericIso.hom.left :=
    ((Over.forget (Spec (.of K))).mapIso D₁.toModel.genericIso).isIso_hom
  have hirr₁ : IrreducibleSpace ((Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).obj M₁).left :=
    D₁.toModel.genericIso.hom.left.homeomorph.irreducibleSpace_iff.mpr inferInstance
  obtain ⟨z, htz, hc⟩ := @GroupConnectedSpread.Abelian.group_model_with_good_open_eventually_connected R K _ _ _ _ t
    M₁ groupM₁ hsm₁ hproper₁ hirr₁ (F.obj V) hconn₁ (F.map i) hopen₁
  exact ⟨EmbeddedCoefficientEnlargement.Abelian.enlargeEmbeddedCoefficientModel D₁ z htz,
    EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_smooth D₁.toModel z htz,
    EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_proper D₁.toModel z htz, hc⟩

end

/-! An actual arithmetic group family through every complex abelian
variety, including geometric connectedness and a group-preserving fiber
comparison. No existence or descent assumption is supplied as input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

structure GeometricGroupCoefficientModel (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) where
  data : AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel ℚ ℂ A.toOver A.variety.presentation.ambientDimension
  group : GrpObj data.toModel.model
  commutative : IsCommMonObj data.toModel.model
  smooth : Smooth data.toModel.model.hom
  proper : IsProper data.toModel.model.hom
  connected : GeometricallyConnected data.toModel.model.hom
  comparison_group :
    letI := group
    letI : GrpObj ((Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ data.toModel.coefficients)).obj
      data.toModel.model) := Functor.grpObjObj
        (F := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ data.toModel.coefficients))
        (G := data.toModel.model)
    IsMonHom data.toModel.genericIso.hom

attribute [instance] GeometricGroupCoefficientModel.group GeometricGroupCoefficientModel.commutative
  GeometricGroupCoefficientModel.smooth GeometricGroupCoefficientModel.proper
  GeometricGroupCoefficientModel.connected GeometricGroupCoefficientModel.comparison_group

theorem abelian_variety_has_geometric_group_coefficient_model (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Nonempty (GeometricGroupCoefficientModel A) := by
  have : Smooth A.toOver.hom := inferInstanceAs (Smooth A.variety.structureMap)
  have : IsIntegral A.toOver.left := A.variety.property
  obtain ⟨D₀, hs₀, hp₀, hc₀⟩ := integral_group_has_connected_embedded_coefficient_model
    ℚ ℂ A.toOver _ (EmbeddedGroupCoefficients.Abelian.abelianProjectiveEmbedding A)
  let M := D₀.toModel.model
  let s := D₀.toModel.coefficients
  let H := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ s)
  have : Smooth M.hom := hs₀
  have : IsProper M.hom := hp₀
  have : GeometricallyConnected M.hom := hc₀
  let genericGroup : GrpObj (H.obj M) := GrpObj.ofIso D₀.toModel.genericIso.symm
  have : IsCommMonObj (H.obj M) := Models.SpreadingOut.GroupReflection.Construction.commutative_group_of_iso D₀.toModel.genericIso.symm
  obtain ⟨t, h, groupN, hcomm, hgroup⟩ := AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GroupModels.Coefficients.commutative_group_model_after_enlargement M
  let F := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ ℂ h)
  let G := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ t)
  let N := F.obj M
  let := groupN
  let : GrpObj (G.obj N) := Functor.grpObjObj (F := G)
  let c : G.obj N ≅ H.obj M := (AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericMorphisms.Coefficients.coefficientGenericComparison (R₀ := ℚ) h).app M
  have hc : IsMonHom c.hom := Models.SpreadingOut.GroupReflection.Construction.image_group_iso_isMonHom G N (H.obj M) c groupN hgroup
  have he : IsMonHom D₀.toModel.genericIso.hom :=
    Models.SpreadingOut.GroupReflection.Construction.transported_group_iso_isMonHom D₀.toModel.genericIso
  have : Smooth N.hom := inferInstanceAs (Smooth (pullback.snd M.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ ℂ h)))
  have : IsProper N.hom := inferInstanceAs (IsProper (pullback.snd M.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ ℂ h)))
  let DN : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel ℚ ℂ A.toOver := {
    coefficients := t
    model := N
    finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
    genericIso := c ≪≫ D₀.toModel.genericIso }
  let DE := EmbeddedCoefficientEnlargement.Abelian.enlargeEmbeddedCoefficientModel D₀ t h
  let D : AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel ℚ ℂ A.toOver A.variety.presentation.ambientDimension := {
    toModel := DN
    embedding := DE.embedding
    closedImmersion := DE.closedImmersion }
  exact ⟨{
    data := D
    group := groupN
    commutative := hcomm
    smooth := inferInstanceAs (Smooth (pullback.snd M.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ ℂ h)))
    proper := inferInstanceAs (IsProper (pullback.snd M.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ ℂ h)))
    connected := inferInstanceAs (GeometricallyConnected (pullback.snd M.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap ℚ ℂ h)))
    comparison_group := inferInstanceAs (IsMonHom (c.hom ≫ D₀.toModel.genericIso.hom)) }⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ConnectedEmbeddedCoefficients.Abelian
