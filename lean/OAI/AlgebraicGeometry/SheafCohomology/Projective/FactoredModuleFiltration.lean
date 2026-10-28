import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleSectionFiltration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FactoredPushforwardOpenModule
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredModuleScalarChange
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePushforward

/-! # Factored Module Filtration -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FactoredModuleFiltration.Dimension

noncomputable section

/-! The polynomial filtration of a composite finite pushforward uses the actual intermediate affine ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePushforward.Construction

universe u

local instance factoredProjectiveModuleFiltrationMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [LinearOrder σ] in
theorem factoredProjective_weightedPiece_eq
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X Z : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Proj (homogeneousSubmodule σ R)) (j : σ)
    {r : ℕ} (w : Fin r → Γ((Scheme.Modules.pushforward (f ≫ a)).obj
      (Invertible.Scheme.Modules.unitObj X), MvPolynomialClosure.MvPolynomial.coordinateOpen j)) (d : Fin r → ℕ) (n : ℕ) :
    letI := hfield.toField
    let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
    let N := (Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X)
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
    letI := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule f a π U
    letI := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule_tower f a π U
    ModuleSectionFiltration.Dimension.projectiveChartWeightedModulePiece hfield N j w d n =
      HomogeneousGeneratorImage.Dimension.weightedPolynomialModulePiece (FilteredSections.Dimension.closedProjectiveChartCoordinates a j)
        (show Fin r → (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N from w) d n := by
  let := hfield.toField
  let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let N := (Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X)
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleScalarTower π N U
  let := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule f a π U
  let := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule_tower f a π U
  apply iSup_congr
  intro i
  exact FilteredModuleScalarChange.Dimension.polynomialFilteredModule_change_scalars
    (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsPullbackAlgHom a π U) (FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule_smul f a π U)
    (fun k => ChartScalars.Dimension.projectiveChartPolynomialAlgHom (R := R) j (MvPolynomial.X k)) _ (n - d i)

theorem factoredProjective_normalized_image_eventually_weighted [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X Z : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsFinite (f ≫ a)] (j : σ) :
    letI := hfield.toField
    let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
    let N := (Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X)
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
    letI := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule f a π U
    letI := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule_tower f a π U
    ∃ (r : ℕ) (w : Fin r → (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N) (d : Fin r → ℕ) (b : ℕ),
      Submodule.span Γ(Z, a ⁻¹ᵁ U) (Set.range w) = ⊤ ∧
      ∀ n, b ≤ n → (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear π N
        (UnitSection.Dimension.projectiveTwistUnitSection j n) U).range =
          HomogeneousGeneratorImage.Dimension.weightedPolynomialModulePiece (FilteredSections.Dimension.closedProjectiveChartCoordinates a j) w d n := by
  let := hfield.toField
  let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let N := (Scheme.Modules.pushforward (f ≫ a)).obj (Invertible.Scheme.Modules.unitObj X)
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleScalarTower π N U
  let := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule f a π U
  let := FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule_tower f a π U
  have : (Invertible.Scheme.Modules.unitObj X).IsQuasicoherent := ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf X)
  have : N.IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (f ≫ a)
  have : (Invertible.Scheme.Modules.unitObj X).IsFiniteType := PolynomialQuotient.Dimension.isFiniteType_of_isLineBundle _
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf X)
  have : N.IsFiniteType := ArithmeticGeometry.OrdinaryLocus.Openness.FinitePushforward.Construction.finitePushforward_isFiniteType (f ≫ a) (Invertible.Scheme.Modules.unitObj X)
  obtain ⟨r, w, d, b, hw, hb⟩ := ModuleSectionFiltration.Dimension.projective_module_normalized_image_eventually_weighted hfield N j
  refine ⟨r, w, d, b, ?_, fun n hn => (hb n hn).trans
    (factoredProjective_weightedPiece_eq hfield f a j w d n)⟩
  exact FilteredModuleScalarChange.Dimension.span_eq_top_of_factored_scalars (a.app U).hom
    (FactoredPushforwardOpenModule.Dimension.factoredPushforwardOpenModule_smul f a π U) (Set.range w) hw

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FactoredModuleFiltration.Dimension
