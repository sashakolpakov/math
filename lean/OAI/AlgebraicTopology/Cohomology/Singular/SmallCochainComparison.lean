import OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual
import OAI.AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective
import OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularCochains
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso

/-! # Small Cochain Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainComparison

noncomputable section

/-!
# The open-cover comparison for actual singular cochains

The proved inclusion of small integral singular chains is a quasi-isomorphism.
Duality with injective integer-module coefficients therefore proves the actual
cochain restriction is a quasi-isomorphism. Characteristic-zero fields are
divisible as additive groups, so this applies to rational and complex
coefficients. Exact scalar restriction identifies those integer-coefficient
models with ordinary rational and complex cochains.
-/

open _root_.CategoryTheory

open OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularCochains OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- With injective integer-module coefficients, actual cochain restriction to
an open cover's small singular simplices is a quasi-isomorphism. -/
theorem smallSingularRestriction_quasiIso_int (M : ModuleCat.{0} ℤ) [Injective M]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X U) := by
  have : QuasiIso (EvaluationNaturality.simplicialScalarChainMap (R := ℤ) (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U)) :=
    AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso.Cycles.smallIntegralChainInclusion_quasiIso X U hopen hcover
  exact InjectiveChainDual.simplicialPullback_quasiIso_of_injective M (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U)

/-- Exact scalar restriction upgrades the integer-module comparison to the
original coefficient module, whenever its underlying integer module is injective. -/
theorem smallSingularRestriction_quasiIso_of_injectiveRestriction
    {R : Type} [CommRing R] (f : ℤ →+* R) (M : ModuleCat.{0} R)
    [Injective ((ModuleCat.restrictScalars f).obj M)]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X U) := by
  let F := ModuleCat.restrictScalars f
  have hq := smallSingularRestriction_quasiIso_int X U (F.obj M) hopen hcover
  have hmap : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X U)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (IntegralCoefficientInjective.simplicialCochainsRestrictScalarsArrowIso f M (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U))).mpr hq
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X U) F).mp hmap

/-- Ordinary singular cochain restriction over a characteristic-zero field is
a quasi-isomorphism for every actual open cover. -/
theorem smallSingularRestriction_quasiIso (F : Type) [Field F] [CharZero F]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction (ModuleCat.of F F) X U) := by
  have := IntegralCoefficientInjective.injective_restrictScalars_field F (algebraMap ℤ F)
  exact smallSingularRestriction_quasiIso_of_injectiveRestriction X U
    (algebraMap ℤ F) (ModuleCat.of F F) hopen hcover

/-- The rational singular cochain comparison for an actual open cover. -/
theorem rationalSmallSingularRestriction_quasiIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction (ModuleCat.of ℚ ℚ) X U) :=
  smallSingularRestriction_quasiIso X U ℚ hopen hcover

/-- The ordinary complex-module singular cochain comparison for an actual open cover. -/
theorem complexSmallSingularRestriction_quasiIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction (ModuleCat.of ℂ ℂ) X U) :=
  smallSingularRestriction_quasiIso X U ℂ hopen hcover

/-- Restriction induces the canonical isomorphism from ordinary singular
cohomology to the cohomology of small singular cochains. -/
def smallSingularCohomologyIso (F : Type) [Field F] [CharZero F]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of F F) X n ≅
      DeRham.Comparison.SmallSingularCochains.smallSingularCohomology (ModuleCat.of F F) X U n := by
  have := smallSingularRestriction_quasiIso X U F hopen hcover
  exact isoOfQuasiIsoAt (DeRham.Comparison.SmallSingularCochains.smallSingularRestriction (ModuleCat.of F F) X U) n

/-- The comparison's forward map is precisely the installed cohomology
restriction, not a separately chosen isomorphism. -/
@[simp]
theorem smallSingularCohomologyIso_hom (F : Type) [Field F] [CharZero F]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (smallSingularCohomologyIso X U F hopen hcover n).hom =
      DeRham.Comparison.SmallSingularCochains.smallSingularCohomologyRestriction (ModuleCat.of F F) X U n := rfl

/-- Actual cohomology restriction is bijective in every degree. -/
theorem smallSingularCohomologyRestriction_bijective (F : Type) [Field F] [CharZero F]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Function.Bijective (DeRham.Comparison.SmallSingularCochains.smallSingularCohomologyRestriction (ModuleCat.of F F) X U n) :=
  (smallSingularCohomologyIso X U F hopen hcover n).toLinearEquiv.bijective

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainComparison
