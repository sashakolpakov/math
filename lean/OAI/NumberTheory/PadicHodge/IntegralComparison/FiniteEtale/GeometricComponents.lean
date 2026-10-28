import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.GeometricFiber
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FrobeniusPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConnectedComponents

/-! # Geometric Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.GeometricComponents

noncomputable section

/-! Geometric prime ideals identify with the actual connected components, including their original Frobenius action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]

local notation "Ω" => AlgebraicClosure k
local notation "T" => Ω ⊗[k] A
local notation "f" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "Y" => OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry.geometricFiber (L := Ω) f

local instance : IsArtinianRing T := IsArtinianRing.of_finite Ω T

def equiv : PrimeSpectrum T ≃ _root_.ConnectedComponents Y := by
  let h : Y ≃ₜ PrimeSpectrum T := Scheme.homeoOfIso (Affine.GeometricFiber.iso k A)
  exact
    { toFun := fun i => ConnectedComponents.mk (h.symm i)
      invFun := h.continuous.connectedComponentsLift
      left_inv := h.apply_symm_apply
      right_inv := by
        intro c
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
        exact congrArg ConnectedComponents.mk (h.symm_apply_apply x) }

theorem equiv_apply (i : PrimeSpectrum T) :
    equiv k A i = ConnectedComponents.mk ((Affine.GeometricFiber.iso k A).inv i) := rfl

theorem scalar (σ : Ω ≃ₐ[k] Ω) (i : PrimeSpectrum T) :
    IntegralComparison.Etale.ConnectedComponents.permutation Y (Frobenius.Geometry.geometricFiberIso f σ) (equiv k A i) =
      equiv k A (i.comap (FrobeniusAlgebra.scalarMap k A σ).toRingHom) := by
  change ConnectedComponents.mk ((Frobenius.Geometry.geometricFiberIso f σ).hom
    ((Affine.GeometricFiber.iso k A).inv i)) =
      ConnectedComponents.mk ((Affine.GeometricFiber.iso k A).inv
        (Spec.map (CommRingCat.ofHom (FrobeniusAlgebra.scalarMap k A σ).toRingHom) i))
  exact congrArg ConnectedComponents.mk (congrArg (fun g : Spec (CommRingCat.of T) ⟶ Y => g i)
    (Affine.GeometricFiber.scalar_natural k A σ))

variable (p a : ℕ) [Fact p.Prime] [Fintype k] [CharP k p] (hcard : Fintype.card k = p ^ a)
  [Nontrivial A] [Algebra.Etale k A]

theorem frobenius (i : PrimeSpectrum T) :
    equiv k A (WittPermutation.permutation k A
      (FrobeniusPolynomial.frobenius p k A) i) =
        IntegralComparison.Etale.ConnectedComponents.permutation Y
          (Frobenius.Geometry.geometricFiberIso f (Frobenius.Geometry.geometricFrobenius p a k hcard))
          (equiv k A i) := by
  exact (congrArg (equiv k A) (FrobeniusAlgebra.comap k A p a hcard i)).trans
    (scalar k A (Frobenius.Geometry.geometricFrobenius p a k hcard) i).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.GeometricComponents
