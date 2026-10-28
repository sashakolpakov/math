import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.StructureModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.CechMorphismDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModelComparisonDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModelAxisCycleLifting
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOrdinaryBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.AbelianGeometricIntegrality

/-! # Product Model Cycle Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ProductModelCycleLifting

noncomputable section

/-! The two normalized axes lift every residue section cycle of a line
bundle on a varying product of projective abelian schemes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
variable {g h : ℕ} (A : Schemes.AbelianScheme g S) (B : Schemes.AbelianScheme h S)
variable [A.scheme.left.IsSeparated] [B.scheme.left.IsSeparated]
variable [(pullback A.scheme.hom B.scheme.hom).IsSeparated]
variable (PA : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
variable {ι κ : Type u} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → A.scheme.left.Opens) (V : κ → B.scheme.left.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
variable (sA : S ⟶ A.scheme.left) (hsA : sA ≫ A.scheme.hom = 𝟙 _)
variable (sB : S ⟶ B.scheme.left) (hsB : sB ≫ B.scheme.hom = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sA ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sB ⁻¹ᵁ V j₀)
variable (L : Line.Bundles.LineBundle (pullback A.scheme.hom B.scheme.hom))
variable (eA : (L.pullback (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left A.scheme.hom B.scheme.hom sB hsB)).sheaf ≅
  Line.Bundles.structureModule A.scheme.left)
variable (eB : (L.pullback (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right A.scheme.hom B.scheme.hom sA hsA)).sheaf ≅
  Line.Bundles.structureModule B.scheme.left)
variable [LinearOrder (Σ _ : ι, κ)]
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom)
  L.sheaf (Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes.cover A.scheme.hom B.scheme.hom U V))
variable [∀ q, Module.Finite Γ(S, ⊤) (D.X q)]
variable [∀ q, Module.Projective Γ(S, ⊤) (D.X q)]

include PA PB hU hV hcU hcV eA eB i₀ hi₀ j₀ hj₀

theorem abelianProductModel_residue_cycle_lift
    (N : ℕ) (hN : ∀ q, N ≤ q → IsZero (D.X q))
    (hφ : ∀ (M : Type u) [AddCommGroup M] [Module Γ(S, ⊤) M],
      QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map M φ))
    (he : (L.pullback (pullback.fst (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom)
      (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))))).sheaf ≅
        Line.Bundles.structureModule (pullback (pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom)
          (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤)))))
    (z : IsLocalRing.ResidueField Γ(S, ⊤) ⊗[Γ(S, ⊤)] D.X 0)
    (hz : (D.d 0 1).hom.baseChange (IsLocalRing.ResidueField Γ(S, ⊤)) z = 0) :
    ∃ x : D.X 0, D.d 0 1 x = 0 ∧
      (1 : IsLocalRing.ResidueField Γ(S, ⊤)) ⊗ₜ[Γ(S, ⊤)] x = z := by
  obtain ⟨E₁, ψ₁, hq₁, hfin₁, hproj₁, hlift₁⟩ := A.exists_structureModel PA U hcU hU
  obtain ⟨E₂, ψ₂, hq₂, hfin₂, hproj₂, hlift₂⟩ := B.exists_structureModel PB V hcV hV
  have : QuasiIso ψ₁ := hq₁
  have : QuasiIso ψ₂ := hq₂
  let W := Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes.cover A.scheme.hom B.scheme.hom U V
  let π := pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom
  let p := φ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π L.sheaf W).inv
  let p₁ := ψ₁ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) U).inv ≫
    ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor A.scheme.hom U).mapIso eA).inv
  let p₂ := ψ₂ ≫ (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv B.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj B.scheme.left) V).inv ≫
    ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor B.scheme.hom V).mapIso eB).inv
  have : QuasiIso p₁ := inferInstance
  have : QuasiIso p₂ := inferInstance
  let r₁ := Product.CechMorphismDetection.ProductCechMorphismDetection.left A.scheme.hom B.scheme.hom U V L.sheaf sB hsB j₀ hj₀
  let r₂ := Product.CechMorphismDetection.ProductCechMorphismDetection.right A.scheme.hom B.scheme.hom U V L.sheaf sA hsA i₀ hi₀
  let q := ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S (IsLocalRing.ResidueField Γ(S, ⊤))
  have : GeometricallyIntegral (A.pullback q).scheme.hom :=
    Picard.PoincareBundle.AbelianGeometricIntegrality.geometricallyIntegral (A.pullback q)
  have : GeometricallyIntegral (B.pullback q).scheme.hom :=
    Picard.PoincareBundle.AbelianGeometricIntegrality.geometricallyIntegral (B.pullback q)
  have : IsIntegral (pullback A.scheme.hom q) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (A.pullback q).scheme.hom
  have : IsIntegral (pullback B.scheme.hom q) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (B.pullback q).scheme.hom
  let F := ModuleCat.extendScalars (algebraMap Γ(S, ⊤) (IsLocalRing.ResidueField Γ(S, ⊤)))
  let H := F.mapHomologicalComplex (ComplexShape.up ℕ)
  let Q := HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤)) (ComplexShape.up ℕ) 0 1 2
  have : QuasiIso (H.map φ) := Quotients.FiniteDescent.TensorExtensionQuasi.Construction.TensorExtension.quasiIso _ φ hφ
  have : QuasiIsoAt (H.map (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π L.sheaf W).inv) 1 :=
    (F.mapHomotopyEquiv (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv π L.sheaf W)).quasiIsoAt_inv 1
  have hqp : QuasiIsoAt (H.map p) 1 := by
    dsimp only [p]
    rw [H.map_comp]
    infer_instance
  have hp : ShortComplex.QuasiIso (F.mapShortComplex.map (Q.map p)) :=
    (quasiIsoAt_iff' (H.map p) 0 1 2 (by simp) (by simp)).mp hqp
  have hd := Product.CechMorphismDetection.ProductCechMorphismDetection.coefficient_jointly A.scheme.hom B.scheme.hom
    U V sA hsA sB hsB i₀ hi₀ j₀ hj₀ hU hV hcU hcV
    (IsLocalRing.ResidueField Γ(S, ⊤)) L he
  have : ∀ n, Projective (D.X n) := fun n => inferInstance
  obtain ⟨g₁, g₂, hg⟩ := HilbertConstruction.Finite.ModelComparisonDetection.finiteModel_exists_detecting_lifts N hN p p₁ p₂ r₁ r₂ _ hp hd
  have : ∀ n, Module.Finite Γ(S, ⊤) (E₁.X n) := hfin₁
  have : ∀ n, Module.Projective Γ(S, ⊤) (E₁.X n) := hproj₁
  have : ∀ n, Module.Finite Γ(S, ⊤) (E₂.X n) := hfin₂
  have : ∀ n, Module.Projective Γ(S, ⊤) (E₂.X n) := hproj₂
  have : ∀ n, Module.Free Γ(S, ⊤) (D.X n) := fun n => Module.free_of_flat_of_isLocalRing
  have : ∀ n, Module.Free Γ(S, ⊤) (E₁.X n) := fun n => Module.free_of_flat_of_isLocalRing
  have : ∀ n, Module.Free Γ(S, ⊤) (E₂.X n) := fun n => Module.free_of_flat_of_isLocalRing
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₁ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 0))
  have : Module.Free Γ(S, ⊤) (D.sc' 0 1 2).X₁ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (D.X 0))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₂ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 1))
  have : Module.Free Γ(S, ⊤) (D.sc' 0 1 2).X₂ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (D.X 1))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₃ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 2))
  have : Module.Free Γ(S, ⊤) (D.sc' 0 1 2).X₃ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (D.X 2))
  have : Module.Finite Γ(S, ⊤) (E₁.sc' 0 1 2).X₁ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (E₁.X 0))
  have : Module.Free Γ(S, ⊤) (E₁.sc' 0 1 2).X₁ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (E₁.X 0))
  have : Module.Finite Γ(S, ⊤) (E₁.sc' 0 1 2).X₂ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (E₁.X 1))
  have : Module.Free Γ(S, ⊤) (E₁.sc' 0 1 2).X₂ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (E₁.X 1))
  have : Module.Finite Γ(S, ⊤) (E₁.sc' 0 1 2).X₃ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (E₁.X 2))
  have : Module.Free Γ(S, ⊤) (E₁.sc' 0 1 2).X₃ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (E₁.X 2))
  have : Module.Finite Γ(S, ⊤) (E₂.sc' 0 1 2).X₁ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (E₂.X 0))
  have : Module.Free Γ(S, ⊤) (E₂.sc' 0 1 2).X₁ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (E₂.X 0))
  have : Module.Finite Γ(S, ⊤) (E₂.sc' 0 1 2).X₂ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (E₂.X 1))
  have : Module.Free Γ(S, ⊤) (E₂.sc' 0 1 2).X₂ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (E₂.X 1))
  have : Module.Finite Γ(S, ⊤) (E₂.sc' 0 1 2).X₃ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (E₂.X 2))
  have : Module.Free Γ(S, ⊤) (E₂.sc' 0 1 2).X₃ :=
    inferInstanceAs (Module.Free Γ(S, ⊤) (E₂.X 2))
  exact HilbertConstruction.Finite.ModelAxisCycleLifting.finiteModel_axes_lift_cycle (D.sc' 0 1 2) (E₁.sc' 0 1 2) (E₂.sc' 0 1 2)
    (Q.map g₁) (Q.map g₂) hlift₁ hlift₂ hg z hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ProductModelCycleLifting
