import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseFormCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis

/-! # Frame Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameFormBasis

noncomputable section

/-! Coordinate bases for the actual divided-power forms of a smooth
finite-level algebra with étale coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A σ : Type) [CommRing A]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A]
  [LinearOrder σ] [Algebra (MvPolynomial σ (Witt.Ring p k n)) A]
  [IsScalarTower (Witt.Ring p k n)
    (MvPolynomial σ (Witt.Ring p k n)) A]
  [Algebra.FormallyEtale (MvPolynomial σ (Witt.Ring p k n)) A]

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "I" => Ideal.span {(p : A)}
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothDividedPowers.dividedPowers p k n A

def formsEquiv (m : ℕ) : letI := SmoothFrame.Complex.wittAlgebra p k n A;
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W A I δ m ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A m := by
  letI := SmoothFrame.Complex.wittAlgebra p k n A
  letI : IsScalarTower W S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (Principal.BaseFormCoordinates.formsEquiv W A (p : W)
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) I δ
    (SmoothFrame.Complex.ideal_eq p k n A)
    (SmoothDividedPowers.wittBase_isDPMorphism p k n A) m).trans
      (OrdinaryBaseQuotient.Ordinary.formsEquiv W S A Ideal.Quotient.mk_surjective m)

omit [Fintype k] in
theorem formsEquiv_symbol (m : ℕ) (a : A) (v : Fin m → A) :
    letI := SmoothFrame.Complex.wittAlgebra p k n A;
    formsEquiv p k n A m (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W A I δ a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S A a v := by
  let := SmoothFrame.Complex.wittAlgebra p k n A
  let : IsScalarTower W S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  change OrdinaryBaseQuotient.Ordinary.formsEquiv W S A Ideal.Quotient.mk_surjective m
    (Principal.BaseFormCoordinates.formsEquiv W A (p : W)
      (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) I δ
      (SmoothFrame.Complex.ideal_eq p k n A)
      (SmoothDividedPowers.wittBase_isDPMorphism p k n A) m
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W A I δ a v)) = _
  rw [Principal.BaseFormCoordinates.formsEquiv_symbol]
  exact OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol W S A Ideal.Quotient.mk_surjective m a v

def basis (m : ℕ) : letI := SmoothFrame.Complex.wittAlgebra p k n A;
    Module.Basis (Set.powersetCard σ m) A (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W A I δ m) := by
  letI := SmoothFrame.Complex.wittAlgebra p k n A
  exact (Etale.CoordinateFormBasis.basis S A σ m).map (formsEquiv p k n A m).symm

omit [Fintype k] in
theorem basis_apply (m : ℕ) (s : Set.powersetCard σ m) :
    letI := SmoothFrame.Complex.wittAlgebra p k n A;
    basis p k n A σ m s = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W A I δ 1
      (fun j => Etale.CoordinateFormBasis.coordinate S A σ
        (Set.powersetCard.ofFinEmbEquiv.symm s j)) := by
  let := SmoothFrame.Complex.wittAlgebra p k n A
  apply (formsEquiv p k n A m).injective
  rw [basis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, formsEquiv_symbol]
  exact Etale.CoordinateFormBasis.basis_apply S A σ m s

variable (C : Type) [CommRing C] [Algebra k C] (ρ : A →+* C)
  (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Witt.Ring p k n) A (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

def frameBasis (m : ℕ) :
    let F := SmoothFrame.object p A C ρ hρ hker k n hbase
    letI : Algebra W F.ring := F.base.toAlgebra
    Module.Basis (Set.powersetCard σ m) F.ring (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W F.ring F.ideal F.dividedPowers m) :=
  basis p k n A σ m

omit [Fintype k] in
theorem frameBasis_apply (m : ℕ) (s : Set.powersetCard σ m) :
    let F := SmoothFrame.object p A C ρ hρ hker k n hbase
    letI : Algebra W F.ring := F.base.toAlgebra
    frameBasis p k n A σ C ρ hρ hker hbase m s = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W F.ring F.ideal F.dividedPowers 1
      (fun j => Etale.CoordinateFormBasis.coordinate S A σ
        (Set.powersetCard.ofFinEmbEquiv.symm s j)) :=
  basis_apply p k n A σ m s

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameFormBasis
