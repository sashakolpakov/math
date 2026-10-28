import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: dimension of the global deformation and support deformations

Actual open immersion charts and the proved constants maps identify the
global structure morphisms with the affine coefficient-field actions.
The one-parameter transcendence calculation therefore gives the exact
global dimension increase, including for singular integral supports.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- An actual deformation chart determines the global dimension increase. -/
theorem deformation_dimension_of_chart (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] (I : Ideal R)
    {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (a : Spec (CommRingCat.of R) ⟶ A) [IsOpenImmersion a]
    (b : Spec (CommRingCat.of (Iff.BundleCycles.deformationAlgebra I)) ⟶ B) [IsOpenImmersion b]
    (g : B ⟶ A)
    (h : b ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R (Iff.BundleCycles.deformationAlgebra I))) ≫ a)
    (f : A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (g ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let α : CommRingCat.of k ⟶ CommRingCat.of R := Spec.preimage (a ≫ f)
  let : Algebra k R := α.hom.toAlgebra
  have hα : Spec.map α = a ≫ f := Spec.map_preimage _
  have hfα : LocallyOfFiniteType (Spec.map α) :=
    (congrArg (fun q => LocallyOfFiniteType q) hα).mpr inferInstance
  have : Algebra.FiniteType k R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hfα
  let := Transcendence.BundleCycles.deformationScalarAlgebra I k
  let c : CommRingCat.of R ⟶ CommRingCat.of (Iff.BundleCycles.deformationAlgebra I) :=
    CommRingCat.ofHom (algebraMap R (Iff.BundleCycles.deformationAlgebra I))
  have hαc : α ≫ c = CommRingCat.ofHom (algebraMap k (Iff.BundleCycles.deformationAlgebra I)) := rfl
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k (Iff.BundleCycles.deformationAlgebra I))) =
      Spec.map c ≫ (a ≫ f) :=
    (congrArg Spec.map hαc.symm).trans
      ((Spec.map_comp α c).trans (congrArg (fun q => Spec.map c ≫ q) hα))
  have hb : b ≫ (g ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap k (Iff.BundleCycles.deformationAlgebra I))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ f) h).trans ((Category.assoc _ _ _).trans hspec.symm))
  have haDim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = (Algebra.trdeg k R).toNat :=
    (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion a f).symm.trans
      ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hα.symm).trans
        (Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra k R))
  exact (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion b (g ≫ f)).symm.trans
    ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hb).trans
    ((Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra k (Iff.BundleCycles.deformationAlgebra I)).trans
    ((Transcendence.BundleCycles.deformationAlgebra_trdeg_toNat I k).trans (congrArg (fun n => n + 1) haDim.symm))))

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual global deformation of an integral scheme has one additional dimension. -/
theorem globalDeformation_dimension (I : X.IdealSheafData) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let x : X := Classical.choice inferInstance
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.AffineZariskiSite := ⟨U, hU⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDomain Γ(X, U) := inferInstance
  have : IsOpenImmersion ((Global.Deformation.BundleCycles.globalDeformationCover I).f V) :=
    Global.DeformationProperties.BundleCycles.globalDeformationCover_isOpenImmersion I V
  have hbase : (Global.Deformation.BundleCycles.globalDeformationCover I).f V ≫ Global.Deformation.BundleCycles.globalDeformationProjection I =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Iff.BundleCycles.deformationAlgebra (I.ideal V))))) ≫ hU.fromSpec := by
    have h0 : (Global.Deformation.BundleCycles.globalDeformationCover I).f V ≫ Global.Deformation.BundleCycles.globalDeformationProjection I =
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Iff.BundleCycles.deformationAlgebra (I.ideal V)))) ≫
          hU.isoSpec.inv) ≫ U.ι := (Global.Deformation.BundleCycles.deformationGlueData I).ι_toBase V
    exact h0.trans ((Category.assoc _ _ _).trans
      (congrArg (fun q => Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Iff.BundleCycles.deformationAlgebra (I.ideal V)))) ≫ q) hU.isoSpec_inv_ι))
  exact @deformation_dimension_of_chart k _ Γ(X, U) _ _ (I.ideal V)
    X (Global.Deformation.BundleCycles.globalDeformation I) _ _ hU.fromSpec inferInstance
    ((Global.Deformation.BundleCycles.globalDeformationCover I).f V) (Global.DeformationProperties.BundleCycles.globalDeformationCover_isOpenImmersion I V)
    (Global.Deformation.BundleCycles.globalDeformationProjection I) hbase f inferInstance

/-- The global deformation of a singular integral closed support has exactly one additional dimension. -/
theorem globalSupportDeformation_dimension (I P : X.IdealSheafData) [IsIntegral P.subscheme]
    (f : P.subscheme ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ f) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let x : P.subscheme := Classical.choice inferInstance
  obtain ⟨U, y, _⟩ := P.subschemeCover.openCover.exists_eq x
  have : Nonempty (Spec ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) := ⟨y⟩
  have : IsDomain ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) := Support.Integrality.BundleCycles.supportCoefficientRing_isDomain P U
  have : IsOpenImmersion (Support.Projection.BundleCycles.supportCoefficientChart P U) :=
    Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion P U
  have : IsOpenImmersion ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U) :=
    Global.SupportDeformation.BundleCycles.globalSupportDeformationCover_isOpenImmersion I P U
  exact @deformation_dimension_of_chart k _ ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) _ _
    (Support.CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) P.subscheme (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) _ _
    (Support.Projection.BundleCycles.supportCoefficientChart P U) (Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion P U)
    ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U) (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover_isOpenImmersion I P U)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport_on_chart I P U) f inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension.BundleCycles
