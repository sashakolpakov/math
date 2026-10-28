import OAI.AlgebraicTopology.Cohomology.Singular.Chains
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Basic.Complex.Basic

/-! # Integral Coefficient Injective -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective

noncomputable section

/-!
# Integral injectivity of characteristic-zero field coefficients

Divisible abelian groups are injective as integer modules by the proved Baer
criterion. In particular, rational and complex coefficients are injective
after restricting scalars to the integers. We also record naturality of the
actual scalar-restriction cochain comparison for arbitrary simplicial maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction commutes with pullback of actual simplicial cochains. -/
theorem simplicialCochainsRestrictScalarsIso_naturality
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{0} S) {K L : SSet.{0}} (g : K ⟶ L) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Functor.simplicialPullback M g) ≫ (Chains.simplicialCochainsRestrictScalarsIso f K M).hom =
      (Chains.simplicialCochainsRestrictScalarsIso f L M).hom ≫
        Functor.simplicialPullback ((ModuleCat.restrictScalars f).obj M) g := by
  let F := ModuleCat.restrictScalars.{0} f
  have h := Chains.simplicialChainsComparison_naturality F.op g (op M)
  ext n : 1
  apply Quiver.Hom.op_inj
  simpa [Chains.simplicialCochainsRestrictScalarsIso, Chains.simplicialChainsComparisonIso,
    Functor.simplicialPullback, Functor.simplicialCochainsFunctor, HomologicalComplex.unopFunctor, F] using
    (congrArg (fun z => z.f n) h).symm

/-- The actual simplicial pullback maps are identified by the canonical
scalar-restriction isomorphisms at their source and target. -/
def simplicialCochainsRestrictScalarsArrowIso
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{0} S) {K L : SSet.{0}} (g : K ⟶ L) :
    Arrow.mk (((ModuleCat.restrictScalars f).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Functor.simplicialPullback M g)) ≅
      Arrow.mk (Functor.simplicialPullback ((ModuleCat.restrictScalars f).obj M) g) :=
  Arrow.isoMk (Chains.simplicialCochainsRestrictScalarsIso f L M)
    (Chains.simplicialCochainsRestrictScalarsIso f K M)
    (simplicialCochainsRestrictScalarsIso_naturality f M g).symm

/-- A divisible integer module is an injective object in the actual module
category. The proof uses Baer's criterion through the equivalence with
abelian groups. -/
theorem injective_intModule_of_divisible (M : ModuleCat.{0} ℤ)
    [DivisibleBy M ℤ] : CategoryTheory.Injective M := by
  apply ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.map_injective_iff M).mp
  change CategoryTheory.Injective (AddCommGrpCat.of M)
  exact AddCommGrpCat.injective_of_divisible M

/-- Any characteristic-zero field, restricted along any integer ring map,
is injective as an integer module. -/
theorem injective_restrictScalars_field (F : Type) [Field F] [CharZero F]
    (f : ℤ →+* F) :
    CategoryTheory.Injective ((ModuleCat.restrictScalars f).obj (ModuleCat.of F F)) := by
  let : DivisibleBy ((ModuleCat.restrictScalars f).obj (ModuleCat.of F F)) ℤ :=
    inferInstanceAs (DivisibleBy F ℤ)
  apply injective_intModule_of_divisible

/-- Rational coefficients are injective over the integers. -/
theorem injective_restrictScalars_rat :
    CategoryTheory.Injective
      ((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).obj (ModuleCat.of ℚ ℚ)) :=
  injective_restrictScalars_field ℚ (algebraMap ℤ ℚ)

/-- Complex coefficients are injective over the integers. -/
theorem injective_restrictScalars_complex :
    CategoryTheory.Injective
      ((ModuleCat.restrictScalars (algebraMap ℤ ℂ)).obj (ModuleCat.of ℂ ℂ)) :=
  injective_restrictScalars_field ℂ (algebraMap ℤ ℂ)

end

end OAI.AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective
