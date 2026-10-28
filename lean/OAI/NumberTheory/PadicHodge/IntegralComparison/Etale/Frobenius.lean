import OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

/-! # Frobenius -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

noncomputable section

/-!
# IntegralComparison: geometric Frobenius on rational pro-étale cohomology

The operator is induced on Ext by the exact equivalence of sheaf categories
coming from the actual automorphism of the geometric fiber. No traces or
characteristic polynomials are specified as part of the construction.
The Frobenius convention follows https://stacks.math.columbia.edu/tag/03SL:
the inverse q-power field automorphism acts by cohomological pullback.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u v w

section ExtTransport

variable (R : Type*) [CommRing R]
variable {C : Type*} [Category C] [Abelian C] [Linear R C] [HasExt.{w} C]

/-- Transport both arguments of Ext by actual isomorphisms. -/
def extIsoCongr {A A' B B' : C} (iA : A ≅ A') (iB : B ≅ B') (n : ℕ) :
    Ext A B n ≃ₗ[R] Ext A' B' n where
  toFun α := ((Ext.mk₀ iA.inv).comp α (Nat.zero_add n)).comp
    (Ext.mk₀ iB.hom) (Nat.add_zero n)
  invFun α := ((Ext.mk₀ iA.hom).comp α (Nat.zero_add n)).comp
    (Ext.mk₀ iB.inv) (Nat.add_zero n)
  left_inv α := by simp
  right_inv α := by simp
  map_add' α β := by simp
  map_smul' r α := by simp

end ExtTransport

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {X Y : Scheme.{u}}

/-- The continuous rational coefficient sheaf is preserved by base transport. -/
def coefficientSheafTransport (e : X ≅ Y) :
    (ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ)) e).functor.obj
      (Cohomology.rationalCoefficientSheaf ℓ X) ≅ Cohomology.rationalCoefficientSheaf ℓ Y :=
  eqToIso rfl

/-- Constant rank-one sheaves are preserved by the same transport. -/
def constantUnitTransport (e : X ≅ Y) :
    (ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ)) e).functor.obj
      (Cohomology.constantUnitSheaf ℓ X) ≅ Cohomology.constantUnitSheaf ℓ Y :=
  (ProEtale.proEtaleSheafCongr_constant (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ)) e).app
    (ModuleCat.of (Cohomology.Coeff.{u} ℓ) (Cohomology.Coeff.{u} ℓ))

/-- Covariant transport of cohomology by a scheme isomorphism. It is the
pullback along the inverse isomorphism. -/
def cohomologyTransport (e : X ≅ Y) (n : ℕ) :
    Cohomology.RationalEllAdicCohomology ℓ X n ≃ₗ[Cohomology.Coeff.{u} ℓ]
      Cohomology.RationalEllAdicCohomology ℓ Y n :=
  (LinearEquiv.ofBijective
    ((ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ)) e).functor.mapExtLinearMap
      (Cohomology.Coeff.{u} ℓ) (Cohomology.constantUnitSheaf ℓ X) (Cohomology.rationalCoefficientSheaf ℓ X) n)
    ((ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (Cohomology.Coeff.{u} ℓ)) e).functor.mapExt_bijective_of_preservesInjectiveObjects
      _ _ n)).trans
    (extIsoCongr (Cohomology.Coeff.{u} ℓ) (constantUnitTransport ℓ e)
      (coefficientSheafTransport ℓ e) n)

/-- Cohomological pullback for a scheme isomorphism. -/
def cohomologyPullback (e : X ≅ Y) (n : ℕ) :
    Cohomology.RationalEllAdicCohomology ℓ Y n ≃ₗ[Cohomology.Coeff.{u} ℓ]
      Cohomology.RationalEllAdicCohomology ℓ X n :=
  cohomologyTransport ℓ e.symm n

open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

/-- Geometric Frobenius on the rational pro-étale cohomology of the
geometric fiber. The field automorphism is the inverse of x ↦ x^q. -/
def geometricFrobeniusOnCohomology
    (p a : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [CharP k p]
    (hcard : Fintype.card k = p ^ a)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    Cohomology.RationalEllAdicCohomology ℓ (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) f) n
      ≃ₗ[Cohomology.Coeff.{u} ℓ]
    Cohomology.RationalEllAdicCohomology ℓ (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) f) n :=
  cohomologyPullback ℓ (Frobenius.Geometry.geometricFiberIso f (Frobenius.Geometry.geometricFrobenius p a k hcard)) n

/-- The same actual geometric Frobenius, linear over Q_l itself. -/
def geometricFrobeniusLinear
    (p a : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [CharP k p]
    (hcard : Fintype.card k = p ^ a)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    Cohomology.RationalEllAdicCohomology ℓ (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) f) n
      ≃ₗ[ℚ_[ℓ]]
    Cohomology.RationalEllAdicCohomology ℓ (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) f) n :=
  (geometricFrobeniusOnCohomology ℓ p a k hcard f n).restrictScalars ℚ_[ℓ]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius
