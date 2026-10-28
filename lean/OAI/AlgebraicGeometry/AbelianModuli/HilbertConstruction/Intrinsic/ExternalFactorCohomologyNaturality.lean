import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FourNaturalitySquares
import Mathlib.CategoryTheory.Whiskering
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechNaturality

/-! # External Factor Cohomology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorCohomologyNaturality

noncomputable section

/-! The genuine cohomology isomorphisms for native external open factors commute with the actual parameter restrictions. All four comparison squares use the same proper-factor and ambient covers. -/
open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

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

set_option backward.isDefEq.respectTransparency false in
theorem nativeExternalFactorCohomologyIso_restrict (n : ℕ) :
    (whiskerRight (HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
      (((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).map (homOfLE hU).op).hom))
      (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤))).app
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom (n + 1)).obj L.sheaf) ≫
      (ExternalFactorCohomology.nativeExternalFactorCohomologyIso H L N U' haU' eU' V hV ha he n).hom =
    (ExternalFactorCohomology.nativeExternalFactorCohomologyIso H L N U haU eU V hV ha he n).hom ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) (n + 1)).map
        (Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction
          (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))
          (leOfHom ((Opens.map b.base).map (homOfLE hU)))) := by
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)
  let A' := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U')
  let T := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)
  let T' := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A' ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)
  let τ := whiskerRight (HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
    (((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).map (homOfLE hU).op).hom))
      (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤))
  let C := CoefficientCechComplex.coefficientCechComplex f.appTop.hom L.sheaf V
  let F := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)
  let F₀ := (IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op (b ⁻¹ᵁ U))
  let F₁ := (IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op (b ⁻¹ᵁ U'))
  let r : F₀ ⟶ F₁ := Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F
    (leOfHom ((Opens.map b.base).map (homOfLE hU)))
  let m := (cechComplexFunctor V).map (whiskerLeft (Opens.map a.base).op r.hom)
  let β₀ := AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U V
  let β₁ := AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U' V
  let eC := CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso f.appTop.hom L.sheaf V hV ha n
  let t₀ := (C.sc (n + 1)).mapHomologyIso T
  let t₁ := (C.sc (n + 1)).mapHomologyIso T'
  let k₀ := Additive.CommonCoverCohomology.additiveCommonCoverCohomologyIso a V hV F₀
    (ExternalFactorAcyclicity.nativeExternalFactor_commonCover_acyclic H L N U haU V ha) n
  let k₁ := Additive.CommonCoverCohomology.additiveCommonCoverCohomologyIso a V hV F₁
    (ExternalFactorAcyclicity.nativeExternalFactor_commonCover_acyclic H L N U' haU' V ha) n
  let hτ := HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℕ)).app C) (n + 1)
  let hβ₀ := HomologicalComplex.homologyMap β₀ (n + 1)
  let hβ₁ := HomologicalComplex.homologyMap β₁ (n + 1)
  let hm := HomologicalComplex.homologyMap m (n + 1)
  let hr := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) (n + 1)).map r
  have h₂ : τ.app (C.homology (n + 1)) ≫ t₁.inv = t₀.inv ≫ hτ := by
    change τ.app ((C.sc (n + 1)).homology) ≫ ((C.sc (n + 1)).mapHomologyIso T').inv =
      ((C.sc (n + 1)).mapHomologyIso T).inv ≫
        ShortComplex.homologyMap ((C.sc (n + 1)).mapNatTrans τ)
    rw [ShortComplex.homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]
  have h₃ : hτ ≫ hβ₁ = hβ₀ ≫ hm := by
    change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    calc
      _ = HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ (.up ℕ)).app C ≫ β₁) (n + 1) :=
        (HomologicalComplex.homologyMap_comp _ _ _).symm
      _ = HomologicalComplex.homologyMap (β₀ ≫ m) (n + 1) :=
        congrArg (fun z => HomologicalComplex.homologyMap z (n + 1))
          (AmbientCechNaturality.nativeAmbientExternalCechTensorMap_restrict a b f.appTop.hom g.appTop.hom
            (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf hU V).symm
      _ = _ := HomologicalComplex.homologyMap_comp _ _ _
  have h₄ : hm ≫ k₁.hom = k₀.hom ≫ hr :=
    Additive.CommonCoverCohomology.additiveCommonCoverCohomologyIso_naturality a V hV r
      (ExternalFactorAcyclicity.nativeExternalFactor_commonCover_acyclic H L N U haU V ha)
      (ExternalFactorAcyclicity.nativeExternalFactor_commonCover_acyclic H L N U' haU' V ha) n
  change τ.app _ ≫ (T'.map eC.inv ≫ (t₁.inv ≫ (hβ₁ ≫ k₁.hom))) =
    (T.map eC.inv ≫ (t₀.inv ≫ (hβ₀ ≫ k₀.hom))) ≫ hr
  have result := FourNaturalitySquares.fourNaturalitySquares (T.map eC.inv) t₀.inv hβ₀ k₀.hom
    (T'.map eC.inv) t₁.inv hβ₁ k₁.hom (τ.app _) (τ.app (C.homology (n + 1)))
    hτ hm hr (τ.naturality eC.inv).symm h₂ h₃ h₄
  exact result

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorCohomologyNaturality
