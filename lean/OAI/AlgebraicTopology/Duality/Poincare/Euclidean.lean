import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap
import OAI.AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel
import OAI.AlgebraicTopology.Duality.Poincare.CapAugmentation

/-! # Euclidean -/

namespace OAI.AlgebraicTopology.Duality.Poincare.Euclidean

noncomputable section

/-!
# Poincare duality for complex Euclidean space

The morphism is the actual cap product with the canonical complex orientation.
The degree equation is `p + q = 2 * d`, including complex dimension zero.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical augmentation is the rational degree-zero homology
isomorphism of every path-connected space. -/
def rationalSingularH0Iso (X : TopCat.{0}) [PathConnectedSpace X] :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 0 ≅ ModuleCat.of ℚ ℚ :=
  asIso (X.singularHomology₀ε (C := ModuleCat.{0} ℚ) (ModuleCat.of ℚ ℚ))

@[simp]
theorem rationalSingularH0Iso_hom (X : TopCat.{0}) [PathConnectedSpace X] :
    (rationalSingularH0Iso X).hom =
      X.singularHomology₀ε (C := ModuleCat.{0} ℚ) (ModuleCat.of ℚ ℚ) := rfl

/-- The same canonical augmentation on the actual complex coordinate space. -/
def complexEuclideanRationalH0Iso (d : ℕ) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Fin d → ℂ))).homology 0 ≅
      ModuleCat.of ℚ ℚ :=
  rationalSingularH0Iso (TopCat.of (Fin d → ℂ))

/-- Positive-degree rational singular homology vanishes by the actual
straight-line contraction of complex coordinate space. -/
theorem complexEuclideanRationalHomology_isZero (d q : ℕ) (hq : q ≠ 0) :
    IsZero ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Fin d → ℂ))).homology q) := by
  let : ContractibleSpace (Fin d → ℂ) := AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles.complexNormalModel_contractible d
  exact AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles.isZero_singularHomology_of_contractible (ModuleCat.of ℚ ℚ)
    (TopCat.of (Fin d → ℂ)) q hq

/-- In positive complementary degree the actual cap map is an isomorphism
because both its actual source and actual target vanish. -/
theorem complexEuclideanCap_positiveComplement_isIso (d p q : ℕ)
    (hpq : p + q = 2 * d) (hq : q ≠ 0) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) p q hpq) :=
  (EuclideanCompactCohomology.complexCompactSupportedCohomology_positiveComplement_isZero d p q hpq hq).isIso
    (complexEuclideanRationalHomology_isZero d q hq) _

/-- In top degree the actual cap map is an isomorphism because its composite
with the canonical degree-zero augmentation is the normalized orientation
evaluation isomorphism. -/
theorem complexEuclideanCap_top_isIso (d : ℕ) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ)
      (2 * d) 0 (Nat.add_zero (2 * d))) := by
  let : IsIso (CapAugmentation.rationalH0Augmentation (TopCat.of (Fin d → ℂ))) := by
    change IsIso ((TopCat.of (Fin d → ℂ)).singularHomology₀ε
      (C := ModuleCat.{0} ℚ) (ModuleCat.of ℚ ℚ))
    infer_instance
  let : IsIso (ModuleCat.ofHom
      (EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d).toLinearMap) :=
    (EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d).toModuleIso.isIso_hom
  exact IsIso.of_isIso_fac_right (CapAugmentation.complexManifoldCompactSupportCap_augmentation d)

/-- Poincare duality for complex Euclidean space: the already constructed
cap product with its canonical complex orientation is an isomorphism in
every pair of complementary nonnegative degrees, including `d = 0`. -/
theorem complexEuclideanPoincareDuality_isIso (d p q : ℕ)
    (hpq : p + q = 2 * d) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) p q hpq) := by
  by_cases hq : q = 0
  · subst q
    have hp : p = 2 * d := by simpa only [Nat.add_zero] using hpq
    subst p
    exact complexEuclideanCap_top_isIso d
  · exact complexEuclideanCap_positiveComplement_isIso d p q hpq hq

/-- The actual Euclidean cap-product map packaged as an isomorphism. -/
def complexEuclideanPoincareDuality (d p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) p ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Fin d → ℂ))).homology q := by
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) p q hpq) :=
    complexEuclideanPoincareDuality_isIso d p q hpq
  exact asIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) p q hpq)

@[simp]
theorem complexEuclideanPoincareDuality_hom (d p q : ℕ) (hpq : p + q = 2 * d) :
    (complexEuclideanPoincareDuality d p q hpq).hom =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) p q hpq := rfl

/-- The same genuine cap-product isomorphism as a rational linear equivalence. -/
def complexEuclideanPoincareDualityEquiv (d p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) p ≃ₗ[ℚ]
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Fin d → ℂ))).homology q :=
  (complexEuclideanPoincareDuality d p q hpq).toLinearEquiv

@[simp]
theorem complexEuclideanPoincareDualityEquiv_apply (d p q : ℕ) (hpq : p + q = 2 * d)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) p) :
    complexEuclideanPoincareDualityEquiv d p q hpq c =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) p q hpq c := rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.Euclidean
