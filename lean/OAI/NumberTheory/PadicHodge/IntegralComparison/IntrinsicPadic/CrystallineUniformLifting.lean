import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CohomologyUniformLifting
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OneSmallCrystalline

/-! # Crystalline Uniform Lifting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CrystallineUniformLifting.Intrinsic

noncomputable section

/-! One fixed power of p makes every bounded crystalline degree-one
class lift to the original integral crystalline degree-one group. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "K" => HomologicalComplex₂.total
  (OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

abbrev bounded (n : ℕ) := BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n 1

def quotientEquiv (n : ℕ) :
    (GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.quotient ℤ_[p] K (p : ℤ_[p]) (n+1)).homology 1 ≃+
      bounded p Y n :=
  (HomologicalComplex.homologyMapIso (OrdinaryReduction.IntrinsicOrdinary.iso p X n) 1).toLinearEquiv.toAddEquiv |>.trans
    ((HomologicalComplex.homologyMapIso (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).symm 1).toLinearEquiv.toAddEquiv.trans
      (SmallCohomology.Intrinsic.linearEquiv p X Y f hp I n 1).toAddEquiv)

theorem quotientEquiv_reduction (n : ℕ) (x : (K).homology 1) :
    quotientEquiv p X Y f hp I n
        (GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] K (p : ℤ_[p]) (n+1) 1 x) =
      Balanced.CrystallineCup.Integral.restriction p (ZMod p) Y n 1
        (OneSmallCrystalline.IntrinsicH.equiv p X Y f hp I hprojective x) := by
  change SmallCohomology.Intrinsic.linearEquiv p X Y f hp I n 1
      (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv 1
        (HomologicalComplex.homologyMap (OrdinaryReduction.IntrinsicOrdinary.iso p X n).hom 1
          (GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] K (p : ℤ_[p]) (n+1) 1 x))) = _
  rw [← OrdinaryReduction.IntrinsicOrdinary.reduction_coordinates]
  exact (OneSmallCrystalline.IntrinsicH.square p X Y f hp I hprojective n x).symm

include hp I hprojective in
theorem exists_power : ∃ c : ℕ, ∀ (n : ℕ) (x : bounded p Y n),
    ∃ y : Witt.Crystalline.integralCohomology p (ZMod p) Y 1,
      Balanced.CrystallineCup.Integral.restriction p (ZMod p) Y n 1 y = p^c • x := by
  let : Module.Finite ℤ_[p] ((K).homology 2) := OrdinaryCechUnit.IntrinsicOrdinary.finite p X 2
  obtain ⟨c, hc⟩ := Principal.CohomologyUniformLifting.exists_power ℤ_[p] K (p : ℤ_[p])
    (OrdinaryCechRegularity.IntrinsicOrdinary.total_regular p X) 1
  refine ⟨c, fun n x => ?_⟩
  obtain ⟨z, hz⟩ := hc (n+1) ((quotientEquiv p X Y f hp I n).symm x)
  refine ⟨OneSmallCrystalline.IntrinsicH.equiv p X Y f hp I hprojective z, ?_⟩
  rw [← quotientEquiv_reduction p X Y f hp I hprojective n z, hz]
  have hscalar : (p : ℤ_[p])^c • (quotientEquiv p X Y f hp I n).symm x =
      p^c • (quotientEquiv p X Y f hp I n).symm x := by
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [hscalar, map_nsmul, AddEquiv.apply_symm_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CrystallineUniformLifting.Intrinsic
