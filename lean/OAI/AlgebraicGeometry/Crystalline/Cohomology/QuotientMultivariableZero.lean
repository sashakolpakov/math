import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ConstantsRetraction

/-! # Quotient Multivariable Zero -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableZero.QuotientMultivariablePoincare

noncomputable section

/-!
# Multivariable Poincaré contraction at finite quotient levels

For every base sub-DP ideal L, the actual multivariable quotient PD
de Rham complex is homotopy equivalent to R/L in degree zero.
-/

open _root_.CategoryTheory

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))
  (L : Ideal R) (hL : DividedPowers.IsSubDPIdeal δ L) [Fintype σ]

local notation "B" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.Ring R σ L
local notation "IB" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.ideal R σ I L
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.dividedPowers R σ K h I δ hunit L hL
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk.QuotientMultivariablePrimitive.derivatives R σ K h I δ hunit L
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive R σ K h L
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk.QuotientMultivariablePrimitive.constants R σ L
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient R σ K h L

omit [Fintype σ] in
theorem commute (i j : σ) : Function.Commute (D i) (D j) :=
  QuotientMultivariableD.QuotientMultivariableForms.derivations_commute R σ K h I δ hunit L i j

def tensorComplex : CochainComplex (ModuleCat R) ℕ :=
  Koszul.Tensor.KoszulTensor.complex R σ B D (commute R σ K h I δ hunit L)

local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableZero.QuotientMultivariablePoincare.tensorComplex R σ K h I δ hunit L

def tensorHomotopyEquiv : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (R ⧸ L))) T :=
  Koszul.ConstantsRetraction.KoszulConstantsRetraction.homotopyEquiv R σ B (R ⧸ L) D S
    (commute R σ K h I δ hunit L)
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.derivation_primitive R σ K h I δ hunit L)
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.derivation_primitive_commute R σ K h I δ hunit L)
    (Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.coordinateList σ) (Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.mem_coordinateList σ)
    (c).toLinearMap r (QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient_constants R σ K h L)
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.derivation_constants R σ K h I δ hunit L)
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.coefficientProjection_constants R σ K h I δ hunit L
      (Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.coordinateList σ) (Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.mem_coordinateList σ))

def complexIso : T ≅ PD.DeRham.PDDeRham.complex R B IB ε := by
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact PD.DeRhamTensor.PDDeRhamTensor.complexIso R B σ IB ε (QuotientMultivariableD.QuotientMultivariableForms.coordinate R σ L) D
    (QuotientMultivariableD.QuotientMultivariableForms.D_eq_sum R σ K h I δ hunit L hL)
    (QuotientMultivariableD.QuotientMultivariableForms.basis R σ K h I δ hunit L hL)
    (QuotientMultivariableD.QuotientMultivariableForms.basis_apply R σ K h I δ hunit L hL)
    (commute R σ K h I δ hunit L)

/-- Actual finite-level PD de Rham contraction, including torsion coefficient quotients. -/
def homotopyEquiv : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (R ⧸ L))) (PD.DeRham.PDDeRham.complex R B IB ε) :=
  (tensorHomotopyEquiv R σ K h I δ hunit L).trans (HomotopyEquiv.ofIso (complexIso R σ K h I δ hunit L hL))

def augmentation : (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (R ⧸ L)) ⟶
    PD.DeRham.PDDeRham.complex R B IB ε := (homotopyEquiv R σ K h I δ hunit L hL).hom

instance augmentation_quasiIso : QuasiIso (augmentation R σ K h I δ hunit L hL) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv R σ K h I δ hunit L hL)

def degreeZeroHomologyIso : (PD.DeRham.PDDeRham.complex R B IB ε).homology 0 ≅ ModuleCat.of R (R ⧸ L) :=
  ((homotopyEquiv R σ K h I δ hunit L hL).toHomologyIso 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (ModuleCat.of R (R ⧸ L))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableZero.QuotientMultivariablePoincare
