import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ObjectwiseResolution

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution

noncomputable section

/-!
# The crystalline polynomial frame resolution

The complex uses the actual frame extensions and their affine transition
maps. Its natural augmentation resolves the native crystalline functions
presheaf. The proof uses the integral coordinate contraction objectwise,
allowing the chosen origins to change along crystalline morphisms.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.functions p k X
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.derivative p k B σ a
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.primitive p k B σ a
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.derivatives W σ F D
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.coefficients p k B σ a
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.retraction p k B σ a

omit [Fintype σ] in
theorem commute (Q : Cᵒᵖ) (i j : σ) : Function.Commute (d Q i) (d Q j) :=
  FreeDivided.Derivation.FreeDividedDerivation.derivations_commute Q.unop.thickening.ring σ i j

omit [Fintype σ] in
theorem rightInverse (Q : Cᵒᵖ) (i : σ) (t : (F).obj Q) : d Q i (S Q i t) = t :=
  FreeDivided.Primitive.FreeDividedPrimitive.derivation_primitive Q.unop.thickening.ring σ i t

omit [Fintype σ] in
theorem commute_primitive (Q : Cᵒᵖ) (i j : σ) (hji : j ≠ i) (t : (F).obj Q) :
    d Q j (S Q i t) = S Q i (d Q j t) :=
  LinearMap.congr_fun (FreeDivided.Primitive.FreeDividedPrimitive.derivation_primitive_commute Q.unop.thickening.ring σ i j hji.symm) t

omit [Fintype σ] in
theorem coefficient_split (Q : Cᵒᵖ) : (r Q).comp ((c).app Q).hom = LinearMap.id :=
  PolynomialResolution.CrystallinePolynomialResolution.coefficient_split p k X σ Q

omit [Fintype σ] in
theorem derivative_coefficients (Q : Cᵒᵖ) (i : σ) (t : (G).obj Q) : d Q i (((c).app Q).hom t) = 0 :=
  Derivation.map_algebraMap (FreeDivided.Derivation.FreeDividedDerivation.derivation Q.unop.thickening.ring σ i) t

omit [Fintype σ] in
theorem successive_apply (Q : Cᵒᵖ) (l : List σ) (t : (F).obj Q) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (S Q) l t =
      FreeDivided.Constants.FreeDividedConstants.successive Q.unop.thickening.ring σ l t := by
  induction l generalizing t with
  | nil => rfl
  | cons i l ih =>
    change Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (S Q) l
      (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection W σ ((F).obj Q) (d Q) i (S Q i) t) =
        FreeDivided.Constants.FreeDividedConstants.successive Q.unop.thickening.ring σ l
          (FreeDivided.Primitive.FreeDividedPrimitive.projection Q.unop.thickening.ring σ i t)
    rw [ih]
    congr 1
    exact LinearMap.congr_fun (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateProjection Q.unop.thickening.ring σ i) t

omit [Fintype σ] in
theorem finalProjection (Q : Cᵒᵖ) (l : List σ) (hl : ∀ i, i ∈ l) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (S Q) l =
      ((c).app Q).hom.comp (r Q) := by
  apply LinearMap.ext
  intro t
  rw [successive_apply, FreeDivided.Constants.FreeDividedConstants.successive_eq_constants _ σ l hl]
  have hc := LinearMap.congr_fun
    (PolynomialResolution.CrystallinePolynomialResolution.augmentation_eq_constantCoefficient p k X σ Q) t
  change algebraMap Q.unop.thickening.ring
    (DividedPowerAlgebra Q.unop.thickening.ring (σ →₀ Q.unop.thickening.ring))
    (FreeDivided.Constants.FreeDividedConstants.constantCoefficient Q.unop.thickening.ring σ t) =
      algebraMap Q.unop.thickening.ring
        (DividedPowerAlgebra Q.unop.thickening.ring (σ →₀ Q.unop.thickening.ring))
        (Multivariable.Reduction.MultivariableReduction.augmentation Q.unop.thickening.ring σ t)
  rw [← hc]
  rfl

def complex : CochainComplex (Cᵒᵖ ⥤ ModuleCat W) ℕ :=
  Koszul.Functor.KoszulFunctor.complex W σ F D (commute p k B σ a)

/-- The actual native crystalline functions map into the frame-coordinate complex. -/
def augmentation : (CochainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat W)).obj G ⟶ complex p k B σ a :=
  Koszul.ObjectwiseResolution.KoszulObjectwiseResolution.augmentation W σ F G D S (commute p k B σ a)
    (rightInverse p k B σ a) (commute_primitive p k B σ a)
    (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateList σ) (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ)
    c r (coefficient_split p k B σ a) (derivative_coefficients p k B σ a)
    (fun Q => finalProjection p k B σ a Q _ (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ))

instance augmentation_quasiIso : QuasiIso (augmentation p k B σ a) :=
  Koszul.ObjectwiseResolution.KoszulObjectwiseResolution.augmentation_quasiIso W σ F G D S (commute p k B σ a)
    (rightInverse p k B σ a) (commute_primitive p k B σ a)
    (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateList σ) (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ)
    c r (coefficient_split p k B σ a) (derivative_coefficients p k B σ a)
    (fun Q => finalProjection p k B σ a Q _ (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution
