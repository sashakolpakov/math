import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.CoefficientFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Frobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearTensor
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexComposition

/-! # Rational Polynomial -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial.RationalPolynomialCoefficientFrobenius

noncomputable section

/-!
# The semilinear polynomial Frobenius over the original Witt fraction field

Witt-coefficient Frobenius is an isomorphism after completion and scalar
extension. Composing it with the proved polynomial substitution gives
a quasi-isomorphism into the Frobenius-twisted scalar structure.
-/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing W
local notation "φ" => WittVector.frobeniusEquiv p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.completedComplex p k σ

def scalarEquiv : K₀ ≃+* K₀ := IsFractionRing.ringEquivOfRingEquiv φ

local instance baseInverse : RingHomInvPair (φ).toRingHom (φ).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv φ
local instance baseInverseSymm : RingHomInvPair (φ).symm.toRingHom (φ).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm φ
local instance fieldInverse : RingHomInvPair (scalarEquiv p k).toRingHom (scalarEquiv p k).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (scalarEquiv p k)
local instance fieldInverseSymm : RingHomInvPair (scalarEquiv p k).symm.toRingHom (scalarEquiv p k).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (scalarEquiv p k)

theorem scalarEquiv_base (w : W) :
    scalarEquiv p k (algebraMap W K₀ w) = algebraMap W K₀ (φ w) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ w

abbrev complex := ((IntrinsicScalarExtension.functor W K₀).mapHomologicalComplex (.up ℕ)).obj C

def formsEquiv (n : ℕ) : (K₀ ⊗[W] (C).X n) ≃ₛₗ[(scalarEquiv p k).toRingHom] (K₀ ⊗[W] (C).X n) :=
  NumberTheory.PadicHodge.GeometricComparison.SemilinearTensor.SemilinearTensorExtension.equiv φ (scalarEquiv p k) (scalarEquiv_base p k)
    (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.completedFormsEquiv p k σ n)

theorem formsEquiv_tmul (n : ℕ) (a : K₀) (ω : (C).X n) :
    formsEquiv p k σ n (a ⊗ₜ[W] ω) = scalarEquiv p k a ⊗ₜ[W]
      (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.completedMap p k σ).f n ω := rfl

def complexMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map (scalarEquiv p k).toRingHom
    (complex p k σ) (complex p k σ) where
  f n := (formsEquiv p k σ n).toLinearMap
  comm i j x := by
    change formsEquiv p k σ j (((C).d i j).hom.baseChange K₀ x) =
      ((C).d i j).hom.baseChange K₀ (formsEquiv p k σ i x)
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a ω =>
      rw [LinearMap.baseChange_tmul, formsEquiv_tmul, formsEquiv_tmul, LinearMap.baseChange_tmul]
      exact congrArg (fun z : (C).X j => scalarEquiv p k a ⊗ₜ[W] z)
        ((WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.completedMap p k σ).comm i j ω)

def linearMap : complex p k σ ⟶ NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex
    (scalarEquiv p k).toRingHom (complex p k σ) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (complexMap p k σ)

instance component_isIso (n : ℕ) : IsIso ((linearMap p k σ).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (formsEquiv p k σ n).bijective

instance linearMap_isIso : IsIso (linearMap p k σ) := HomologicalComplex.Hom.isIso_of_components _

def coefficientIso : complex p k σ ≅ NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex
    (scalarEquiv p k).toRingHom (complex p k σ) := asIso (linearMap p k σ)

variable [Fintype σ]

def ordinaryComplexIso : complex p k σ ≅ Polynomial.Frobenius.PolynomialFrobenius.ordinaryComplex p k σ := Iso.refl _

def substitution : complex p k σ ⟶ complex p k σ :=
  (ordinaryComplexIso p k σ).hom ≫ Polynomial.Frobenius.PolynomialFrobenius.ordinaryFrobenius p k σ ≫
    (ordinaryComplexIso p k σ).inv

instance substitution_quasiIso : QuasiIso (substitution p k σ) := by
  unfold substitution
  infer_instance

def frobenius : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map (scalarEquiv p k).toRingHom
    (complex p k σ) (complex p k σ) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexComposition.precompLinear (substitution p k σ) (complexMap p k σ)

omit [Fintype σ] in
theorem frobenius_linearMap :
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (frobenius p k σ) =
      substitution p k σ ≫ linearMap p k σ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  rfl

instance frobenius_quasiIso :
    QuasiIso (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (frobenius p k σ)) := by
  rw [frobenius_linearMap]
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial.RationalPolynomialCoefficientFrobenius
