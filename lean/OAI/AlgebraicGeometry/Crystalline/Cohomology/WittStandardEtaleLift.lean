import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham

/-! # Witt Standard Etale Lift -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittStandardEtaleLift.PerfectWittStandardEtaleLift

noncomputable section

/-! # Standard etale Witt frames over an arbitrary perfect residue field -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ C : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [CommRing C] [Algebra k C] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] (P : StandardEtalePresentation (MvPolynomial σ k) C)

local notation "W" => WittVector p k
local notation "S" => MvPolynomial σ k
local notation "R" => MvPolynomial σ W
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift.Ring p k σ C P
local notation "ρ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift.reduction p k σ C P

omit [Algebra k C] [IsScalarTower k S C] in
theorem reduction_kernel : RingHom.ker ρ = Ideal.span {(p : A)} := by
  have h : RingHom.ker ρ =
      RingHom.ker (NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLiftAlgebra.reduction S
        (NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift.residue_surjective p k σ) P.P) :=
    RingHom.ker_comp_of_injective _
      (show Function.Injective P.equivRing.symm.toRingHom from P.equivRing.symm.injective)
  rw [h, NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLiftAlgebra.reduction_kernel]
  change (RingHom.ker (MvPolynomial.map (WittVector.constantCoeff : W →+* k))).map
    (algebraMap R A) = _
  rw [MvPolynomial.ker_map, WittVector.ker_constantCoeff,
    Ideal.map_span, Set.image_singleton, map_natCast,
    Ideal.map_span, Set.image_singleton, map_natCast]

omit [CharP k p] [PerfectRing k p] [Algebra k C] [IsScalarTower k S C] in
theorem smooth [Finite σ] : Algebra.Smooth W A := by
  let : Fintype σ := Fintype.ofFinite σ
  let : Algebra.Smooth W R := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp W R A

omit [CharP k p] [PerfectRing k p] [Algebra k C] [IsScalarTower k S C] in
theorem flat [Finite σ] : Module.Flat W A := by
  let := smooth p k σ C P
  exact Algebra.Smooth.flat W A

variable [Fintype σ] [LinearOrder σ]

def homologyIso (n i : ℕ) :
    (NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.deRhamComplex p k A n).homology i ≅
      ModuleCat.of (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))
        (NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
          (J := Ideal.span {(p : W)}) (δ := Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
          (NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)) n i) := by
  let := PerfectWittStandardEtaleLift.flat p k σ C P
  exact NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.homologyIso p k A C σ ρ
    (NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift.reduction_surjective p k σ C P)
    (reduction_kernel p k σ C P)
    (NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift.reduction_base p k σ C P) n i

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittStandardEtaleLift.PerfectWittStandardEtaleLift
