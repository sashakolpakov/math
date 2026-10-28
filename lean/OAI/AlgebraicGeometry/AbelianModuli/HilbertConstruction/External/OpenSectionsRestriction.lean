import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.OpenSectionsLinearity

/-! # Open Sections Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.OpenSectionsRestriction

noncomputable section

/-! The linear external-section comparison commutes with restriction to a
smaller affine parameter open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
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

theorem externalOpenSectionsModuleIso_hom :
    (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)).map (OpenSectionsLinearity.externalOpenSectionsModuleIso H L N U haU eU V hV ha he).hom =
      (Intrinsic.ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U haU eU V hV ha he 0).hom ≫
        (Cech.FactorDegreeZero.IntrinsicCech.cechFactorZeroCohomologyIso
          (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)) (b ⁻¹ᵁ U)).hom := rfl

variable (U' : Y.Opens) (haU' : IsAffineOpen U')
variable (eU' : (Scheme.Modules.pullback U'.ι).obj N.sheaf ≅ Line.Bundles.structureModule U'.toScheme)
variable [Module.Flat Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U'))]

theorem externalOpenSectionsModuleIso_restrict (hU : U' ≤ U) :
    (tensorRight ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf)).map
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).map (homOfLE hU).op) ≫
        (OpenSectionsLinearity.externalOpenSectionsModuleIso H L N U' haU' eU' V hV ha he).hom =
    (OpenSectionsLinearity.externalOpenSectionsModuleIso H L N U haU eU V hV ha he).hom ≫
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp f.appTop.hom)
        (((L.pullback a).tensor (N.pullback b)).sheaf)).map
          ((Opens.map b.base).map (homOfLE hU)).op := by
  let B := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf
  let F := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)
  let hW : b ⁻¹ᵁ U' ≤ b ⁻¹ᵁ U := leOfHom ((Opens.map b.base).map (homOfLE hU))
  let r := Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F hW
  let τ := (Functor.whiskerRight (HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap
    (((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).map (homOfLE hU).op).hom))
      (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤))).app B
  let e₀ := Intrinsic.ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U haU eU V hV ha he 0
  let e₀' := Intrinsic.ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U' haU' eU' V hV ha he 0
  let e₁ := Cech.FactorDegreeZero.IntrinsicCech.cechFactorZeroCohomologyIso F (b ⁻¹ᵁ U)
  let e₁' := Cech.FactorDegreeZero.IntrinsicCech.cechFactorZeroCohomologyIso F (b ⁻¹ᵁ U')
  let q := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map r
  have h₀ : τ ≫ e₀'.hom = e₀.hom ≫ q :=
    Intrinsic.ExternalAllCohomologyNaturality.nativeExternalFactorAllCohomologyIso_restrict H L N hU haU haU' eU eU' V hV ha he 0
  have h₁ : q ≫ e₁'.hom = e₁.hom ≫ F.obj.map (homOfLE hW).op :=
    (Cech.FactorDegreeZero.IntrinsicCech.cechFactorZeroCohomologyPresheafIso F).hom.naturality (homOfLE hW).op
  apply (HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)).map_injective
  rw [Functor.map_comp, Functor.map_comp,
    externalOpenSectionsModuleIso_hom, externalOpenSectionsModuleIso_hom,
    Field.ExternalFactorCechTensor.moduleTensorRight_map_eq_scalarMap]
  change τ ≫ (e₀'.hom ≫ e₁'.hom) = (e₀.hom ≫ e₁.hom) ≫ F.obj.map (homOfLE hW).op
  rw [← Category.assoc, h₀, Category.assoc, h₁, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.OpenSectionsRestriction
