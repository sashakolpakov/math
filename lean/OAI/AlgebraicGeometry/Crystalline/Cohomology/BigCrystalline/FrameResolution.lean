import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ObjectwiseResolution

/-! # Frame Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution

noncomputable section

/-! # A polynomial frame resolution of the original big crystalline functions

The augmentation is an objectwise quasi-isomorphism, proved by integral
free divided-power contraction. Transition maps retain the chosen affine
coordinates and act on the actual big-site coefficient presheaf.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)} (a : σ → A) [Fintype σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor.BigCrystallineFrameFunctor.functions (p := p) (J := J) (δ := δ) (base := base) a
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
  (p := p) (J := J) (δ := δ) base
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators.BigCrystallineFrameOperators.derivative (p := p) (J := J) (δ := δ) (base := base) a
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators.BigCrystallineFrameOperators.primitive (p := p) (J := J) (δ := δ) (base := base) a
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.derivatives W σ F D
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor.BigCrystallineFrameFunctor.coefficients (p := p) (J := J) (δ := δ) (base := base) a
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators.BigCrystallineFrameOperators.retraction (p := p) (J := J) (δ := δ) (base := base) a

omit [Fintype σ] in
theorem commute (Q : Cᵒᵖ) (i j : σ) : Function.Commute (d Q i) (d Q j) :=
  FreeDivided.Derivation.FreeDividedDerivation.derivations_commute Q.unop.ring σ i j

omit [Fintype σ] in
theorem rightInverse (Q : Cᵒᵖ) (i : σ) (t : (F).obj Q) : d Q i (S Q i t) = t :=
  FreeDivided.Primitive.FreeDividedPrimitive.derivation_primitive Q.unop.ring σ i t

omit [Fintype σ] in
theorem commute_primitive (Q : Cᵒᵖ) (i j : σ) (hji : j ≠ i) (t : (F).obj Q) :
    d Q j (S Q i t) = S Q i (d Q j t) :=
  LinearMap.congr_fun (FreeDivided.Primitive.FreeDividedPrimitive.derivation_primitive_commute Q.unop.ring σ i j hji.symm) t

omit [Fintype σ] in
theorem coefficient_split (Q : Cᵒᵖ) : (e Q).comp ((c).app Q).hom = LinearMap.id := by
  apply LinearMap.ext
  intro t
  exact LinearMap.congr_fun (FreeDivided.Constants.FreeDividedConstants.constantCoefficient_constants Q.unop.ring σ) t

omit [Fintype σ] in
theorem derivative_coefficients (Q : Cᵒᵖ) (i : σ) (t : (G).obj Q) : d Q i (((c).app Q).hom t) = 0 :=
  Derivation.map_algebraMap (FreeDivided.Derivation.FreeDividedDerivation.derivation Q.unop.ring σ i) t

omit [Fintype σ] in
theorem successive_apply (Q : Cᵒᵖ) (l : List σ) (t : (F).obj Q) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (S Q) l t =
      FreeDivided.Constants.FreeDividedConstants.successive Q.unop.ring σ l t := by
  induction l generalizing t with
  | nil => rfl
  | cons i l ih =>
    change Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (S Q) l
      (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection W σ ((F).obj Q) (d Q) i (S Q i) t) =
        FreeDivided.Constants.FreeDividedConstants.successive Q.unop.ring σ l
          (FreeDivided.Primitive.FreeDividedPrimitive.projection Q.unop.ring σ i t)
    rw [ih]
    congr 1
    exact LinearMap.congr_fun (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateProjection Q.unop.ring σ i) t

omit [Fintype σ] in
theorem finalProjection (Q : Cᵒᵖ) (l : List σ) (hl : ∀ i, i ∈ l) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ ((F).obj Q) (d Q) (S Q) l =
      ((c).app Q).hom.comp (e Q) := by
  apply LinearMap.ext
  intro t
  rw [successive_apply, FreeDivided.Constants.FreeDividedConstants.successive_eq_constants _ σ l hl]
  rfl

def complex : CochainComplex (Cᵒᵖ ⥤ ModuleCat W) ℕ :=
  Koszul.Functor.KoszulFunctor.complex W σ F D (commute a)

/-- The original big crystalline functions map into the frame-coordinate complex. -/
def augmentation : (CochainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat W)).obj G ⟶ complex a :=
  Koszul.ObjectwiseResolution.KoszulObjectwiseResolution.augmentation W σ F G D S (commute a)
    (rightInverse a) (commute_primitive a)
    (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateList σ) (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ)
    c e (coefficient_split a) (derivative_coefficients a)
    (fun Q => finalProjection a Q _ (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ))

instance augmentation_quasiIso : QuasiIso (augmentation (p := p) (J := J) (δ := δ) (base := base) a) :=
  Koszul.ObjectwiseResolution.KoszulObjectwiseResolution.augmentation_quasiIso W σ F G D S (commute a)
    (rightInverse a) (commute_primitive a)
    (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.coordinateList σ) (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ)
    c e (coefficient_split a) (derivative_coefficients a)
    (fun Q => finalProjection a Q _ (FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.mem_coordinateList σ))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution
