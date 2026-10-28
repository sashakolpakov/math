import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FourNaturalitySquares
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorAllCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorCohomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverZeroNaturality

/-! # External All Cohomology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalAllCohomologyNaturality

noncomputable section

/-! External-factor cohomology comparisons commute with the actual parameter
restrictions in every degree, including degree zero. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S X Y P : Scheme.{u}} [IsAffine S] [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {U U' : Y.Opens} (hU : U' ≤ U)
variable (haU : IsAffineOpen U) (haU' : IsAffineOpen U')
variable (eU : (Scheme.Modules.pullback U.ι).obj N.sheaf ≅ Line.Bundles.structureModule U.toScheme)
variable (eU' : (Scheme.Modules.pullback U'.ι).obj N.sheaf ≅ Line.Bundles.structureModule U'.toScheme)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (ha : ∀ i, IsAffineOpen (V i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable [Module.Flat Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U))]
variable [Module.Flat Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U'))]

theorem nativeExternalFactorZeroCohomologyIso_restrict :
    (Functor.whiskerRight (HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
      (((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).map (homOfLE hU).op).hom))
      (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤))).app
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf) ≫
      (ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U' haU' eU' V hV ha he 0).hom =
    (ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U haU eU V hV ha he 0).hom ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map
        (Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction
          (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))
          (leOfHom ((Opens.map b.base).map (homOfLE hU)))) := by
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)
  let A' := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U')
  let T := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)
  let T' := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A' ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)
  let τ := Functor.whiskerRight (HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
    (((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).map (homOfLE hU).op).hom))
      (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤))
  let C := CoefficientCechComplex.coefficientCechComplex f.appTop.hom L.sheaf V
  let F := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)
  let F₀ := (IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op (b ⁻¹ᵁ U))
  let F₁ := (IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op (b ⁻¹ᵁ U'))
  let r : F₀ ⟶ F₁ := Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F
    (leOfHom ((Opens.map b.base).map (homOfLE hU)))
  let m := (cechComplexFunctor V).map (Functor.whiskerLeft (Opens.map a.base).op r.hom)
  let β₀ := AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U V
  let β₁ := AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U' V
  let eC := (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
    f.appTop.hom L.sheaf).toModuleIso ≪≫
      CoefficientCech.DegreeZeroLinearity.coefficientCechZeroSectionsModuleIso f.appTop.hom L.sheaf V hV
  let t₀ := (C.sc 0).mapHomologyIso T
  let t₁ := (C.sc 0).mapHomologyIso T'
  let k₀ := Additive.CommonCoverDegreeZero.additiveCommonCoverZeroCohomologyIso a V hV F₀
  let k₁ := Additive.CommonCoverDegreeZero.additiveCommonCoverZeroCohomologyIso a V hV F₁
  let hτ := HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℕ)).app C) 0
  let hβ₀ := HomologicalComplex.homologyMap β₀ 0
  let hβ₁ := HomologicalComplex.homologyMap β₁ 0
  let hm := HomologicalComplex.homologyMap m 0
  let hr := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map r
  have h₂ : τ.app (C.homology 0) ≫ t₁.inv = t₀.inv ≫ hτ := by
    change τ.app ((C.sc 0).homology) ≫ ((C.sc 0).mapHomologyIso T').inv =
      ((C.sc 0).mapHomologyIso T).inv ≫
        ShortComplex.homologyMap ((C.sc 0).mapNatTrans τ)
    rw [ShortComplex.homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]
  have h₃ : hτ ≫ hβ₁ = hβ₀ ≫ hm := by
    change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun z => HomologicalComplex.homologyMap z 0)
      (AmbientCechNaturality.nativeAmbientExternalCechTensorMap_restrict a b f.appTop.hom g.appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf hU V).symm
  have h₄ : hm ≫ k₁.hom = k₀.hom ≫ hr :=
    Additive.CommonCoverZeroNaturality.additiveCommonCoverZeroCohomologyIso_naturality a V hV r
  change τ.app _ ≫ (T'.map eC.hom ≫ (t₁.inv ≫ (hβ₁ ≫ k₁.hom))) =
    (T.map eC.hom ≫ (t₀.inv ≫ (hβ₀ ≫ k₀.hom))) ≫ hr
  have result := FourNaturalitySquares.fourNaturalitySquares (T.map eC.hom) t₀.inv hβ₀ k₀.hom
    (T'.map eC.hom) t₁.inv hβ₁ k₁.hom (τ.app _) (τ.app (C.homology 0))
    hτ hm hr (τ.naturality eC.hom).symm h₂ h₃ h₄
  exact result

theorem nativeExternalFactorAllCohomologyIso_restrict (n : ℕ) :
    (Functor.whiskerRight (HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
      (((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).map (homOfLE hU).op).hom))
      (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤))).app
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom n).obj L.sheaf) ≫
      (ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U' haU' eU' V hV ha he n).hom =
    (ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U haU eU V hV ha he n).hom ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) n).map
        (Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction
          (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))
          (leOfHom ((Opens.map b.base).map (homOfLE hU)))) := by
  cases n with
  | zero => exact nativeExternalFactorZeroCohomologyIso_restrict H L N hU haU haU' eU eU' V hV ha he
  | succ n => exact ExternalFactorCohomologyNaturality.nativeExternalFactorCohomologyIso_restrict H L N hU haU haU' eU eU' V hV ha he n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalAllCohomologyNaturality
