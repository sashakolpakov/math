import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveModuleSectionFiltration
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FactoredPushforwardOpenModule
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleScalarChange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveFilteredSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePushforward

/-! # Factored Projective Module Filtration -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FactoredProjectiveModuleFiltration.Construction

noncomputable section

/-! The polynomial filtration of a composite finite pushforward uses the actual intermediate affine ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance factoredProjectiveModuleFiltrationMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [LinearOrder σ] in
theorem factoredProjective_weightedPiece_eq
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X Z : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Proj (homogeneousSubmodule σ R)) (j : σ)
    {r : ℕ} (w : Fin r → Γ((Scheme.Modules.pushforward (f ≫ a)).obj
      (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)) (d : Fin r → ℕ) (n : ℕ) :
    letI := hfield.toField
    let π := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
    let N := (Scheme.Modules.pushforward (f ≫ a)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
    letI := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule f a π U
    letI := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule_tower f a π U
    ProjectiveModuleSectionFiltration.Construction.projectiveChartWeightedModulePiece hfield N j w d n =
      HomogeneousGeneratorImage.Construction.weightedPolynomialModulePiece (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j)
        (show Fin r → (BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N from w) d n := by
  let := hfield.toField
  let π := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let N := (Scheme.Modules.pushforward (f ≫ a)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
  let := BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
  let := BaseOpenModuleTower.Construction.baseOpenModuleScalarTower π N U
  let := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule f a π U
  let := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule_tower f a π U
  apply iSup_congr
  intro i
  exact FilteredModuleScalarChange.Construction.polynomialFilteredModule_change_scalars
    (BaseOpenSections.Construction.baseOpenSectionsPullbackAlgHom a π U) (FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule_smul f a π U)
    (fun k => ProjectiveChartScalars.Construction.projectiveChartPolynomialAlgHom (R := R) j (MvPolynomial.X k)) _ (n - d i)

theorem factoredProjective_normalized_image_eventually_weighted [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤)) {X Z : Scheme.{u}}
    (f : X ⟶ Z) (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsFinite (f ≫ a)] (j : σ) :
    letI := hfield.toField
    let π := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
    let N := (Scheme.Modules.pushforward (f ≫ a)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
    letI := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule f a π U
    letI := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule_tower f a π U
    ∃ (r : ℕ) (w : Fin r → (BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N) (d : Fin r → ℕ) (b : ℕ),
      Submodule.span Γ(Z, a ⁻¹ᵁ U) (Set.range w) = ⊤ ∧
      ∀ n, b ≤ n → (BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear π N
        (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) U).range =
          HomogeneousGeneratorImage.Construction.weightedPolynomialModulePiece (ProjectiveFilteredSections.Construction.closedProjectiveChartCoordinates a j) w d n := by
  let := hfield.toField
  let π := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let N := (Scheme.Modules.pushforward (f ≫ a)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra (a ≫ π) (a ⁻¹ᵁ U)
  let := BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
  let := BaseOpenModuleTower.Construction.baseOpenModuleScalarTower π N U
  let := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule f a π U
  let := FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule_tower f a π U
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsQuasicoherent := LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _
    (LineBundle.Construction.isLineBundle_structureSheaf X)
  have : N.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (f ≫ a)
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsFiniteType := ProjectiveCohomologyFiniteness.Construction.isFiniteType_of_isLineBundle _
    (LineBundle.Construction.isLineBundle_structureSheaf X)
  have : N.IsFiniteType := FinitePushforward.Construction.finitePushforward_isFiniteType (f ≫ a) (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
  obtain ⟨r, w, d, b, hw, hb⟩ := ProjectiveModuleSectionFiltration.Construction.projective_module_normalized_image_eventually_weighted hfield N j
  refine ⟨r, w, d, b, ?_, fun n hn => (hb n hn).trans
    (factoredProjective_weightedPiece_eq hfield f a j w d n)⟩
  exact FilteredModuleScalarChange.Construction.span_eq_top_of_factored_scalars (a.app U).hom
    (FactoredPushforwardOpenModule.Construction.factoredPushforwardOpenModule_smul f a π U) (Set.range w) hw

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FactoredProjectiveModuleFiltration.Construction
