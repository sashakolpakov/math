import OAI.NumberTheory.PadicHodge.GeometricComparison.SurjectiveBase
import OAI.NumberTheory.PadicHodge.GeometricComparison.Residue
import Mathlib.RingTheory.Smooth.Basic

/-! # Witt Algebra -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WittAlgebra.PadicWittAlgebra

noncomputable section

/-! The canonical Witt-to-p-adic coefficient equivalence equips the original
integral algebras with Witt structures and preserves their ordinary complexes. -/

open _root_.CategoryTheory

variable (p : ℕ) [Fact p.Prime]
local notation "W" => WittVector p (ZMod p)

@[instance_reducible]
def coefficientAlgebra : Algebra W ℤ_[p] := (WittVector.equiv p).toRingHom.toAlgebra

local instance coefficients : Algebra W ℤ_[p] := coefficientAlgebra p

def coefficientEquiv : W ≃ₐ[W] ℤ_[p] :=
  { WittVector.equiv p with commutes' := fun _ => rfl }

theorem coefficient_smooth : Algebra.Smooth W ℤ_[p] := Algebra.Smooth.of_equiv (coefficientEquiv p)

variable (A : Type) [CommRing A] [Algebra ℤ_[p] A]

@[instance_reducible]
def algebra : Algebra W A := ((algebraMap ℤ_[p] A).comp (WittVector.equiv p).toRingHom).toAlgebra

local instance sourceAlgebra : Algebra W A := algebra p A
local instance sourceTower : IsScalarTower W ℤ_[p] A := IsScalarTower.of_algebraMap_eq' rfl

theorem smooth [Algebra.Smooth ℤ_[p] A] : Algebra.Smooth W A := by
  let : Algebra.Smooth W ℤ_[p] := coefficient_smooth p
  exact Algebra.Smooth.comp W ℤ_[p] A

theorem flat [Algebra.Smooth ℤ_[p] A] : Module.Flat W A := by
  let : Algebra.Smooth W A := smooth p A
  infer_instance

def deRhamIso : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W A ≅
    ((ModuleCat.restrictScalars (WittVector.equiv p).toRingHom).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex ℤ_[p] A) :=
  SurjectiveBase.SurjectiveBaseDeRham.iso W ℤ_[p] A (WittVector.equiv p).surjective

variable (C : Type) [CommRing C] [Algebra (ZMod p) C] (ρ : A →+* C)
  (hρ : ∀ z : ℤ_[p], ρ (algebraMap ℤ_[p] A z) = algebraMap (ZMod p) C (PadicInt.toZMod z))

include hρ in
theorem reduction_base (w : W) :
    ρ (algebraMap W A w) = algebraMap (ZMod p) C (WittVector.constantCoeff w) :=
  (hρ ((WittVector.equiv p) w)).trans
    (congrArg (algebraMap (ZMod p) C) (RingHom.congr_fun (Residue.PadicBase.wittEquiv_residue p) w))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WittAlgebra.PadicWittAlgebra
