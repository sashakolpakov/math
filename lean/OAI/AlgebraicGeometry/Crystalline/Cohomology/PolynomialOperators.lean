import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Constants

/-! # Polynomial Operators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialOperators.CrystallinePolynomialOperators

noncomputable section

/-!
# Natural coordinate operators on crystalline polynomial functions

Coordinate differentiation and integration are natural endomorphisms of
the actual functions presheaf of the native polynomial extension. The
coefficient maps split naturally, and the coordinate derivatives vanish
on the original crystalline functions.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (σ : Type u)

local notation "W" => WittVector p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X

/-- Actual ambient functions of the polynomial-extension functor. -/
def functions : Cᵒᵖ ⥤ ModuleCat W :=
  (PolynomialFunctor.CrystallinePolynomialFunctor.functor p k X σ).op ⋙ Site.functions p k X

def derivative (i : σ) : functions p k X σ ⟶ functions p k X σ where
  app Q := ModuleCat.ofHom
    ((FreeDivided.Derivation.FreeDividedDerivation.derivation Q.unop.thickening.ring σ i).toLinearMap.restrictScalars W)
  naturality {Q P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    let : Algebra Q.unop.thickening.ring P.unop.thickening.ring := f.unop.ambientMap.toRingHom.toAlgebra
    exact FreeRelative.BaseChange.FreeRelativeBaseChange.derivation_naturality Q.unop.thickening.ring P.unop.thickening.ring σ i a

def primitive (i : σ) : functions p k X σ ⟶ functions p k X σ where
  app Q := ModuleCat.ofHom ((FreeDivided.Primitive.FreeDividedPrimitive.primitive Q.unop.thickening.ring σ i).restrictScalars W)
  naturality {Q P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    let : Algebra Q.unop.thickening.ring P.unop.thickening.ring := f.unop.ambientMap.toRingHom.toAlgebra
    exact FreeRelative.BaseChange.FreeRelativeBaseChange.primitive_naturality Q.unop.thickening.ring P.unop.thickening.ring σ i a

def coefficients : Site.functions p k X ⟶ functions p k X σ where
  app Q := ModuleCat.ofHom
    ((PolynomialThickening.CrystallinePolynomialThickening.inclusion p k Q.unop.residueRing σ Q.unop.thickening).hom.toLinearMap)
  naturality {Q P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (PolynomialFunctor.CrystallinePolynomialFunctor.ambientMap_coefficient σ f.unop a).symm

def augmentation : functions p k X σ ⟶ Site.functions p k X where
  app Q := ModuleCat.ofHom
    ((PolynomialThickening.CrystallinePolynomialThickening.augmentation p k Q.unop.residueRing σ Q.unop.thickening).hom.toLinearMap)
  naturality {Q P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact PolynomialFunctor.CrystallinePolynomialFunctor.augmentation_ambientMap σ f.unop a

theorem coefficients_augmentation : coefficients p k X σ ≫ augmentation p k X σ = 𝟙 _ := by
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (Multivariable.Reduction.MultivariableReduction.augmentation Q.unop.thickening.ring σ).commutes a

theorem derivatives_commute (i j : σ) : derivative p k X σ i ≫ derivative p k X σ j =
    derivative p k X σ j ≫ derivative p k X σ i := by
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact FreeDivided.Derivation.FreeDividedDerivation.derivations_commute Q.unop.thickening.ring σ j i a

theorem primitive_derivative (i : σ) : primitive p k X σ i ≫ derivative p k X σ i = 𝟙 _ := by
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact FreeDivided.Primitive.FreeDividedPrimitive.derivation_primitive Q.unop.thickening.ring σ i a

theorem primitive_derivative_commute (i j : σ) (hij : i ≠ j) :
    primitive p k X σ i ≫ derivative p k X σ j =
      derivative p k X σ j ≫ primitive p k X σ i := by
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact LinearMap.congr_fun
    (FreeDivided.Primitive.FreeDividedPrimitive.derivation_primitive_commute Q.unop.thickening.ring σ i j hij) a

theorem coefficients_derivative (i : σ) : coefficients p k X σ ≫ derivative p k X σ i = 0 := by
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Derivation.map_algebraMap (FreeDivided.Derivation.FreeDividedDerivation.derivation Q.unop.thickening.ring σ i) a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialOperators.CrystallinePolynomialOperators
