import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Transpose
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HypercohomologyMap
import OAI.Analysis.DifferentialForms.Manifold.DeRhamResolution

/-! # De -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De

noncomputable section

section

/-!
# The actual morphism to the analytic de Rham sheaf complex

Canonical extension isomorphisms connect the preserved integer-indexed
algebraic complex with its nonnegative presentation. The already proved
open-section realization then descends along the analytification adjunction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def deRhamPresheafTransposeIso :
    Complex.Transpose.transpose (Algebraic.Sheaves.deRhamPresheafOfComplexes X) ≅ Algebraic.Sheaves.deRhamPresheafComplex X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    rw [Algebraic.Sheaves.deRhamPresheafComplex_d]
    simp only [Iso.refl_hom]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- The preserved algebraic complex is canonically the integer extension of the same sheaf complex. -/
def algebraicSheafIntExtensionIso :
    Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X ≅
      (Algebraic.Sheaves.algebraicDeRhamSheafComplex X).extend (ComplexShape.embeddingUpIntGE 0) :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
      (Complex.Transpose.transposeExtendIso (Algebraic.Sheaves.deRhamPresheafOfComplexes X)
        (ComplexShape.embeddingUpIntGE 0)) ≪≫
    Complex.Extension.mapExtendIso
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ))
      (ComplexShape.embeddingUpIntGE 0) (Complex.Transpose.transpose (Algebraic.Sheaves.deRhamPresheafOfComplexes X)) ≪≫
    ((ComplexShape.embeddingUpIntGE 0).extendFunctor (Algebraic.Sheaves.ComplexSheaves X)).mapIso
      (((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso (deRhamPresheafTransposeIso X))

/-- Inverse image along the actual analytic-to-Zariski point map. -/
def analytificationInverseImage : Algebraic.Sheaves.ComplexSheaves X ⥤ Betti.Smooth.SheafMap.AnalyticComplexSheaves X :=
  TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (Analytification.Base.analytificationMap X)

def analytificationAdjunction : analytificationInverseImage X ⊣ Betti.Smooth.SheafMap.analytificationPushforward X :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℂ) (Analytification.Base.analytificationMap X)

instance analytificationInverseImageIsLeftAdjoint : (analytificationInverseImage X).IsLeftAdjoint :=
  (analytificationAdjunction X).isLeftAdjoint

instance analytificationInverseImagePreservesFiniteLimits :
    PreservesFiniteLimits (analytificationInverseImage X) :=
  Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map (Analytification.Base.analytificationMap X)) (ModuleCat.{0} ℂ)
    (Opens.grothendieckTopology (TopCat.of X.left))
    (Opens.grothendieckTopology (Betti.Scheme.schemePointSpace X))

instance analytificationInverseImagePreservesFiniteColimits :
    PreservesFiniteColimits (analytificationInverseImage X) := inferInstance

instance analytificationInverseImageAdditive : (analytificationInverseImage X).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (analytificationInverseImage X)
  exact (analytificationInverseImage X).additive_of_preservesBinaryBiproducts

def analytificationComplexAdjunctionInt :
    (analytificationInverseImage X).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (Betti.Smooth.SheafMap.analytificationPushforward X).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes (analytificationAdjunction X) (ComplexShape.up ℤ)

variable [IsIntegral X.left] [Smooth X.hom]

/-- The genuine analytic smooth de Rham sheaf complex, extended by zero in negative degrees. -/
def analyticDeRhamSheafComplexInt : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) ℤ :=
  (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).extend
    (ComplexShape.embeddingUpIntGE 0)

/-- The previously proved sheaf realization with the preserved algebraic source. -/
def algebraicToAnalyticDirectImageInt : Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X ⟶
    ((Betti.Smooth.SheafMap.analytificationPushforward X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (analyticDeRhamSheafComplexInt X) := by
  let K : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) ℕ :=
    Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  let e := Complex.Extension.mapExtendIso (Betti.Smooth.SheafMap.analytificationPushforward X)
    (ComplexShape.embeddingUpIntGE 0) K
  exact (algebraicSheafIntExtensionIso X).hom ≫
    HomologicalComplex.extendMap (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap X) (ComplexShape.embeddingUpIntGE 0) ≫
    e.inv

/-- The comparison of actual sheaf complexes on the analytic site. -/
def algebraicToAnalyticSheafMapInt :
    ((analytificationInverseImage X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X) ⟶ analyticDeRhamSheafComplexInt X :=
  ((analytificationComplexAdjunctionInt X).homEquiv (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)
    (analyticDeRhamSheafComplexInt X)).symm (algebraicToAnalyticDirectImageInt X)

theorem algebraicToAnalyticSheafMapInt_normalization :
    (analytificationComplexAdjunctionInt X).homEquiv (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)
      (analyticDeRhamSheafComplexInt X) (algebraicToAnalyticSheafMapInt X) =
        algebraicToAnalyticDirectImageInt X :=
  (analytificationComplexAdjunctionInt X).homEquiv _ _ |>.apply_symm_apply _

end

section

/-! The proved analytic de Rham resolution, with the integer indexing used by BettiComparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def analyticConstantSheaf : Betti.Smooth.SheafMap.AnalyticComplexSheaves X :=
  Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexSheafOn (Betti.Scheme.schemePointSpace X)

instance analyticComplexSheavesHasDerivedCategory : HasDerivedCategory.{1} (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) :=
  HasDerivedCategory.standard _

variable [IsIntegral X.left] [Smooth X.hom]

/-- The actual constant-function augmentation, extended by zero. -/
def analyticDeRhamAugmentationInt :
    (CochainComplex.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (analyticConstantSheaf X) ⟶
      analyticDeRhamSheafComplexInt X :=
  (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntGE 0)
    (analyticConstantSheaf X) 0 0 (by rfl)).inv ≫
    HomologicalComplex.extendMap
      (Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (ComplexShape.embeddingUpIntGE 0)

/-- Invertibility is supplied by the proved analytic Poincaré lemma. -/
instance analyticDeRhamAugmentationInt_quasiIso : QuasiIso (analyticDeRhamAugmentationInt X) := by
  let a : (CochainComplex.single₀ (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)).obj (analyticConstantSheaf X) ⟶
      Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
    Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have ha : QuasiIso a :=
    Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldDeRhamSheafAugmentation_quasiIso (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have : QuasiIso (HomologicalComplex.extendMap a (ComplexShape.embeddingUpIntGE 0)) :=
    (HomologicalComplex.quasiIso_extendMap_iff a (ComplexShape.embeddingUpIntGE 0)).mpr ha
  change QuasiIso ((HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntGE 0)
    (analyticConstantSheaf X) 0 0 (by rfl)).inv ≫
      HomologicalComplex.extendMap a (ComplexShape.embeddingUpIntGE 0))
  infer_instance

/-- The standard analytic constant sheaf is canonically resolved by the actual smooth forms. -/
def analyticDeRhamResolutionIso :
    (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (analyticConstantSheaf X) ≅
      DerivedCategory.Q.obj (analyticDeRhamSheafComplexInt X) := by
  let Q : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) ℤ ⥤ DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) :=
    DerivedCategory.Q
  have : IsIso (Q.map (analyticDeRhamAugmentationInt X)) :=
    Localization.inverts Q (HomologicalComplex.quasiIso (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) (ComplexShape.up ℤ))
      (analyticDeRhamAugmentationInt X) (analyticDeRhamAugmentationInt_quasiIso X)
  let e := asIso (Q.map (analyticDeRhamAugmentationInt X))
  exact e

end

/-!
# The constructed map to analytic constant-sheaf cohomology

Exact inverse image along the actual analytification map is applied to the
preserved algebraic hypercohomology. The explicitly constructed realization
of forms and the proved analytic de Rham resolution then give the map below.
Identification of analytic constant-sheaf cohomology with Betti remains a
separate comparison.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

instance analytificationPushforwardLinear : (Betti.Smooth.SheafMap.analytificationPushforward X).Linear ℂ where
  map_smul := by intros; rfl

instance analytificationInverseImageLinear : (analytificationInverseImage X).Linear ℂ where
  map_smul {M N} c g := by
    let adj := analytificationAdjunction X
    apply (adj.homEquiv M ((analytificationInverseImage X).obj N)).injective
    have hmap (k : M ⟶ N) :
        adj.homEquiv M ((analytificationInverseImage X).obj N)
          ((analytificationInverseImage X).map k) = k ≫ adj.unit.app N := by
      simpa only [Category.comp_id, adj.homEquiv_id] using
        adj.homEquiv_naturality_left k (𝟙 ((analytificationInverseImage X).obj N))
    rw [hmap, Linear.smul_comp, adj.homEquiv_unit,
      Functor.map_smul, Linear.comp_smul, ← adj.homEquiv_unit, hmap]

def derivedAnalytificationInverseImage :
    DerivedCategory (Algebraic.Sheaves.ComplexSheaves X) ⥤ DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) :=
  (analytificationInverseImage X).mapDerivedCategory

instance derivedAnalytificationInverseImageLinear : (derivedAnalytificationInverseImage X).Linear ℂ :=
  inferInstanceAs ((analytificationInverseImage X).mapDerivedCategory.Linear ℂ)

instance derivedAnalytificationInverseImageAdditive : (derivedAnalytificationInverseImage X).Additive :=
  inferInstanceAs ((analytificationInverseImage X).mapDerivedCategory.Additive)

instance derivedAnalytificationInverseImageCommShift :
    (derivedAnalytificationInverseImage X).CommShift ℤ :=
  inferInstanceAs ((analytificationInverseImage X).mapDerivedCategory.CommShift ℤ)

/-- The constant-sheaf identification is the one furnished by the genuine adjunction. -/
def analytificationInverseImageConstantIso :
    (analytificationInverseImage X).obj (Algebraic.Sheaves.constantComplexSheaf X) ≅ analyticConstantSheaf X := by
  have hT : IsTerminal ((Opens.map (Analytification.Base.analytificationMap X)).obj (⊤ : X.left.Opens)) := by
    change IsTerminal (⊤ : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    exact isTerminalTop
  exact (((constantSheafAdj (Opens.grothendieckTopology X.left)
      (ModuleCat.{0} ℂ) isTerminalTop).comp (analytificationAdjunction X)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology (Betti.Scheme.schemePointSpace X)) (ModuleCat.{0} ℂ) hT)).app
      (ModuleCat.of ℂ ℂ)

def derivedAnalytificationConstantIso :
    (derivedAnalytificationInverseImage X).obj
        ((DerivedCategory.singleFunctor (Algebraic.Sheaves.ComplexSheaves X) 0).obj (Algebraic.Sheaves.constantComplexSheaf X)) ≅
      (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (analyticConstantSheaf X) :=
  ((analytificationInverseImage X).mapDerivedCategorySingleFunctor 0).app (Algebraic.Sheaves.constantComplexSheaf X) ≪≫
    (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).mapIso
      (analytificationInverseImageConstantIso X)

/-- Actual derived-category cohomology of the analytic constant complex sheaf. -/
def analyticConstantCohomology (n : ℕ) : ModuleCat.{1} ℂ :=
  ModuleCat.of ℂ
    ((DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (analyticConstantSheaf X) ⟶
      ((DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj
        (analyticConstantSheaf X))⟦(n : ℤ)⟧)

variable [IsIntegral X.left] [Smooth X.hom]

def derivedAlgebraicToAnalyticForms :
    (derivedAnalytificationInverseImage X).obj
        (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)) ⟶
      DerivedCategory.Q.obj (analyticDeRhamSheafComplexInt X) :=
  (analytificationInverseImage X).mapDerivedCategoryFactors.hom.app (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X) ≫
    DerivedCategory.Q.map (algebraicToAnalyticSheafMapInt X)

/-- The actual derived realization followed by the inverse of the proved analytic resolution. -/
def derivedAlgebraicToAnalyticConstant :
    (derivedAnalytificationInverseImage X).obj
        (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)) ⟶
      (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (analyticConstantSheaf X) :=
  derivedAlgebraicToAnalyticForms X ≫ (analyticDeRhamResolutionIso X).inv

/-- Comparison with genuine analytic constant-sheaf cohomology. -/
def algebraicToAnalyticCohomologyMap (n : ℕ) : Algebraic.Sheaves.algebraicDeRham X n ⟶ analyticConstantCohomology X n :=
  ModuleCat.ofHom
    { toFun := fun a =>
        (derivedAnalytificationConstantIso X).inv ≫
          (derivedAnalytificationInverseImage X).map a ≫
          ((derivedAnalytificationInverseImage X).commShiftIso (n : ℤ)).hom.app
            (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)) ≫
          (shiftFunctor (DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)) (n : ℤ)).map
            (derivedAlgebraicToAnalyticConstant X)
      map_add' := by
        intro a b
        simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by
        intro c a
        simp only [Functor.map_smul, Linear.comp_smul, Linear.smul_comp, RingHom.id_apply] }

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De
