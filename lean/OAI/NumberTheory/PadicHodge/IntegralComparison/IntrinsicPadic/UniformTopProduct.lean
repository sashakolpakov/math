import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReductionProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CrystallineUniformLifting
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveProductTorsion
import OAI.NumberTheory.PadicHodge.IntegralComparison.PositiveProductUniformDetection

/-! # Uniform Top Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.UniformTopProduct.Intrinsic

noncomputable section

/-! Cup compatibility and detection by the actual finite comparison maps
transport a nonzero rational ordinary product to the balanced exterior cup. Uniform integral lifting
at every finite level supplies the comparison, with no choice of product
or cohomology groups substituted for the original ones. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

private theorem tensor_eq_zero_of_nsmul
    {R F M : Type*} [CommRing R] [Field F] [CharZero F] [Algebra R F]
    [AddCommGroup M] [Module R M] (a : ℕ) (ha : a ≠ 0) (x : M) (hx : a • x = 0) :
    (1 : F) ⊗ₜ[R] x = 0 := by
  have hs : (a : F) • ((1 : F) ⊗ₜ[R] x) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul, map_nsmul, map_zero, TensorProduct.mk_apply] using
      congrArg (TensorProduct.mk R F M 1) hx
  have h := congrArg (fun y : F ⊗[R] M => (a : F)⁻¹ • y) hs
  have haF : (a : F) ≠ 0 := Nat.cast_ne_zero.mpr ha
  simpa only [smul_smul, inv_mul_cancel₀ haF, one_smul, smul_zero] using h

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hprojective : Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

abbrev ordinary (i : ℕ) :=
  (IntegralDeRham.CechProduct.total ℤ_[p] X
    (NonemptyCechNerve.nerve (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X))).homology i

abbrev ordinaryCup (i j : ℕ) (x : ordinary p X i) (y : ordinary p X j) :=
  IntegralDeRham.CechProduct.cohomologyCup ℤ_[p] X
    (NonemptyCechNerve.nerve (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X)) i j x y

variable
  (hcup : ∀ (n i j : ℕ) (x : ordinary p X i) (y : ordinary p X j),
    ReductionProduct.Intrinsic.reductionComparison p X Y f hp n (i+j)
        (ordinaryCup p X i j x y) =
      Balanced.SmoothProperWittCup.cup p (ZMod p) Y n i j
        (ReductionProduct.Intrinsic.reductionComparison p X Y f hp n i x)
        (ReductionProduct.Intrinsic.reductionComparison p X Y f hp n j y))
  (hdetect : ∀ (i : ℕ) (x : ordinary p X i),
    (∀ n : ℕ, ReductionProduct.Intrinsic.reductionComparison p X Y f hp n i x = 0) →
      x = 0)

include hp hcup hdetect in
theorem exteriorPowerCup_ne_zero (d : ℕ) (v : Fin (d+1) → ordinary p X 1)
    (hv : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] GradedPositiveProduct.product (ordinaryCup p X) d v ≠ 0) :
    GradedExteriorCup.exteriorPowerCup
      (Balanced.RationalCupUnit.data p (ZMod p) Y hprojective) (d+1) ≠ 0 := by
  classical
  intro hz
  let I := injectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y))
  obtain ⟨c, hc⟩ := CrystallineUniformLifting.Intrinsic.exists_power p X Y f hp I hprojective
  obtain ⟨b, hb⟩ := Balanced.PositiveProductTorsion.uniform p (ZMod p) Y hprojective d hz
  have ht : p^(b+c*(d+1)) • GradedPositiveProduct.product (ordinaryCup p X) d v = 0 := by
    simpa only [pow_add, pow_mul] using
      PositiveProductUniformDetection.annihilation
        (ordinaryCup p X)
        (fun i j x y => Balanced.CrystallineCup.Integral.cup p (ZMod p) Y hprojective i j x y)
        (fun n => Balanced.SmoothProperWittCup.cup p (ZMod p) Y n)
        (fun n i => ReductionProduct.Intrinsic.reductionComparison p X Y f hp n i)
        (fun n i => (Balanced.CrystallineCup.Integral.restriction p (ZMod p) Y n i).toAddMonoidHom)
        hcup
        (Balanced.CrystallineCup.Integral.restriction_cup p (ZMod p) Y hprojective)
        hdetect
        d (p^b) (p^c) hc hb v
  exact hv (tensor_eq_zero_of_nsmul (R := ℤ_[p]) (F := ℚ_[p]) _
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) _ ht)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.UniformTopProduct.Intrinsic
