import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FourNaturalitySquares
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorAllCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverZeroNaturality

/-! # External Zero Cohomology Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalZeroCohomologyScalars

noncomputable section

/-! The external-factor comparison in degree zero intertwines the actual
coefficient scalar with the scalar endomorphism of the open-factor sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X Y P : Scheme.{u}} [IsAffine S] [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable (U : Y.Opens) (haU : IsAffineOpen U)
variable (eU : (Scheme.Modules.pullback U.ι).obj N.sheaf ≅ Line.Bundles.structureModule U.toScheme)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens) (hV : iSup V = ⊤)
variable (ha : ∀ i, IsAffineOpen (V i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable [Module.Flat Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U))]

theorem nativeExternalFactorZeroCohomologyIso_scalar (r : Γ(S, ⊤)) :
    (Functor.whiskerRight (HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
      (r • (LinearMap.id : ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)) →ₗ[Γ(S, ⊤)]
        ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U))))) (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤))).app
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf) ≫
        (ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U haU eU V hV ha he 0).hom =
    (ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U haU eU V hV ha he 0).hom ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map
        (AmbientCechScalars.nativeAmbientFactorScalar a b f.appTop.hom L.sheaf N.sheaf U r) := by
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)
  let T := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)
  let τ := Functor.whiskerRight (HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
    (r • (LinearMap.id : A →ₗ[Γ(S, ⊤)] A))) (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤))
  let C := CoefficientCechComplex.coefficientCechComplex f.appTop.hom L.sheaf V
  let F := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)
  let F₀ := (IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op (b ⁻¹ᵁ U))
  let s : F₀ ⟶ F₀ := AmbientCechScalars.nativeAmbientFactorScalar a b f.appTop.hom L.sheaf N.sheaf U r
  let m := (cechComplexFunctor V).map (Functor.whiskerLeft (Opens.map a.base).op s.hom)
  let β : (T.mapHomologicalComplex (.up ℕ)).obj C ⟶
      (cechComplexFunctor V).obj ((Opens.map a.base).op ⋙ F₀.obj) :=
    AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U V
  let eC := (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
    f.appTop.hom L.sheaf).toModuleIso ≪≫
      CoefficientCech.DegreeZeroLinearity.coefficientCechZeroSectionsModuleIso f.appTop.hom L.sheaf V hV
  let t := (C.sc 0).mapHomologyIso T
  let k := Additive.CommonCoverDegreeZero.additiveCommonCoverZeroCohomologyIso a V hV F₀
  let hτ := HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℕ)).app C) 0
  let hβ := HomologicalComplex.homologyMap β 0
  let hm := HomologicalComplex.homologyMap m 0
  let hs := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map s
  have h₂ : τ.app (C.homology 0) ≫ t.inv = t.inv ≫ hτ := by
    change τ.app ((C.sc 0).homology) ≫ ((C.sc 0).mapHomologyIso T).inv =
      ((C.sc 0).mapHomologyIso T).inv ≫ ShortComplex.homologyMap ((C.sc 0).mapNatTrans τ)
    rw [ShortComplex.homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]
  have h₃ : hτ ≫ hβ = hβ ≫ hm := by
    change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp ((NatTrans.mapHomologicalComplex τ (.up ℕ)).app C) β,
      ← HomologicalComplex.homologyMap_comp β m]
    exact congrArg (fun z => HomologicalComplex.homologyMap z 0)
      (AmbientCechScalars.nativeAmbientExternalCechTensorMap_scalar a b f.appTop.hom g.appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U r V).symm
  have h₄ : hm ≫ k.hom = k.hom ≫ hs :=
    Additive.CommonCoverZeroNaturality.additiveCommonCoverZeroCohomologyIso_naturality a V hV s
  change τ.app _ ≫ (T.map eC.hom ≫ (t.inv ≫ (hβ ≫ k.hom))) =
    (T.map eC.hom ≫ (t.inv ≫ (hβ ≫ k.hom))) ≫ hs
  have result := FourNaturalitySquares.fourNaturalitySquares (T.map eC.hom) t.inv hβ k.hom
    (T.map eC.hom) t.inv hβ k.hom (τ.app _) (τ.app (C.homology 0))
    hτ hm hs (τ.naturality eC.hom).symm h₂ h₃ h₄
  exact result

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalZeroCohomologyScalars
