import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialOperators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.FunctorResolution

/-! # Polynomial Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialResolution.CrystallinePolynomialResolution

noncomputable section

/-!
# A coordinate resolution of native crystalline functions

Natural coordinate primitives on actual polynomial extensions give an
augmented complex of presheaves whose coefficient object is the original
native crystalline functions presheaf. Its augmentation is a
quasi-isomorphism. The differential acts in the adjoined coordinates and
annihilates the original ambient functions.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (σ : Type u) [Fintype σ]

local notation "W" => WittVector p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialOperators.CrystallinePolynomialOperators.functions p k X σ
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.functions p k X
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialOperators.CrystallinePolynomialOperators.derivative p k X σ
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialOperators.CrystallinePolynomialOperators.primitive p k X σ
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.derivatives W σ F D
local notation "s" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.derivatives W σ F S
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialOperators.CrystallinePolynomialOperators.coefficients p k X σ
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialOperators.CrystallinePolynomialOperators.augmentation p k X σ

omit [Fintype σ] in
theorem commute (Q : Cᵒᵖ) (i j : σ) : Function.Commute (d Q i) (d Q j) :=
  FreeDivided.Derivation.FreeDividedDerivation.derivations_commute Q.unop.thickening.ring σ i j

omit [Fintype σ] in
theorem rightInverse (Q : Cᵒᵖ) (i : σ) (a : (F).obj Q) : d Q i (s Q i a) = a :=
  FreeDivided.Primitive.FreeDividedPrimitive.derivation_primitive Q.unop.thickening.ring σ i a

omit [Fintype σ] in
theorem commute_primitive (Q : Cᵒᵖ) (i j : σ) (hji : j ≠ i) (a : (F).obj Q) :
    d Q j (s Q i a) = s Q i (d Q j a) :=
  LinearMap.congr_fun (FreeDivided.Primitive.FreeDividedPrimitive.derivation_primitive_commute Q.unop.thickening.ring σ i j hji.symm) a

omit [Fintype σ] in
theorem coefficient_split (Q : Cᵒᵖ) : ((r).app Q).hom.comp ((c).app Q).hom = LinearMap.id := by
  apply LinearMap.ext
  intro a
  exact (Multivariable.Reduction.MultivariableReduction.augmentation Q.unop.thickening.ring σ).commutes a

omit [Fintype σ] in
theorem derivative_coefficients (Q : Cᵒᵖ) (i : σ) (a : (G).obj Q) : d Q i (((c).app Q).hom a) = 0 :=
  Derivation.map_algebraMap (FreeDivided.Derivation.FreeDividedDerivation.derivation Q.unop.thickening.ring σ i) a

omit [Fintype σ] in
theorem successive_apply (Q : Cᵒᵖ) (l : List σ) (a : (F).obj Q) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (s Q) l a =
      FreeDivided.Constants.FreeDividedConstants.successive Q.unop.thickening.ring σ l a := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    change Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (s Q) l
      (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection W σ ((F).obj Q) (d Q) i (s Q i) a) =
        FreeDivided.Constants.FreeDividedConstants.successive Q.unop.thickening.ring σ l
          (FreeDivided.Primitive.FreeDividedPrimitive.projection Q.unop.thickening.ring σ i a)
    rw [ih]
    congr 1
    exact LinearMap.congr_fun (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateProjection Q.unop.thickening.ring σ i) a

omit [Fintype σ] in
theorem augmentation_eq_constantCoefficient (Q : Cᵒᵖ) :
    (Multivariable.Reduction.MultivariableReduction.augmentation Q.unop.thickening.ring σ).toLinearMap =
      FreeDivided.Constants.FreeDividedConstants.constantCoefficient Q.unop.thickening.ring σ := by
  apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top Q.unop.thickening.ring σ)
  rintro _ ⟨e, rfl⟩
  exact (Multivariable.Reduction.MultivariableReduction.augmentation_monomial Q.unop.thickening.ring σ e).trans
    (FreeDivided.Constants.FreeDividedConstants.constantCoefficient_monomial Q.unop.thickening.ring σ e).symm

omit [Fintype σ] in
theorem finalProjection (Q : Cᵒᵖ) (l : List σ) (hl : ∀ i, i ∈ l) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (s Q) l =
      ((c).app Q).hom.comp ((r).app Q).hom := by
  apply LinearMap.ext
  intro a
  rw [successive_apply, FreeDivided.Constants.FreeDividedConstants.successive_eq_constants _ σ l hl]
  have hc := LinearMap.congr_fun (augmentation_eq_constantCoefficient p k X σ Q) a
  change algebraMap Q.unop.thickening.ring
    (DividedPowerAlgebra Q.unop.thickening.ring (σ →₀ Q.unop.thickening.ring))
    (FreeDivided.Constants.FreeDividedConstants.constantCoefficient Q.unop.thickening.ring σ a) =
      algebraMap Q.unop.thickening.ring
        (DividedPowerAlgebra Q.unop.thickening.ring (σ →₀ Q.unop.thickening.ring))
        (Multivariable.Reduction.MultivariableReduction.augmentation Q.unop.thickening.ring σ a)
  rw [← hc]
  rfl

def complex : CochainComplex (Cᵒᵖ ⥤ ModuleCat W) ℕ :=
  Koszul.Functor.KoszulFunctor.complex W σ F D (commute p k X σ)

/-- The coefficient presheaf is the original native crystalline functions. -/
def augmentation : (CochainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat W)).obj G ⟶ complex p k X σ :=
  Koszul.FunctorResolution.KoszulFunctorResolution.augmentation W σ F G D S (commute p k X σ)
    (rightInverse p k X σ) (commute_primitive p k X σ)
    (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateList σ) (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ)
    c r (coefficient_split p k X σ) (derivative_coefficients p k X σ)
    (fun Q => finalProjection p k X σ Q _ (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ))

instance augmentation_quasiIso : QuasiIso (augmentation p k X σ) :=
  Koszul.FunctorResolution.KoszulFunctorResolution.augmentation_quasiIso W σ F G D S (commute p k X σ)
    (rightInverse p k X σ) (commute_primitive p k X σ)
    (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateList σ) (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ)
    c r (coefficient_split p k X σ) (derivative_coefficients p k X σ)
    (fun Q => finalProjection p k X σ Q _ (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialResolution.CrystallinePolynomialResolution
