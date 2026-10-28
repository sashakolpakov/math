import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.RelativeIsomorphismTensorCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.CoefficientFiberIsomorphism

/-! # Local Closed Fiber Isomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.LocalClosedFiberIsomorphism

noncomputable section

/-! A finite affine morphism over a noetherian local target is an
isomorphism when its coefficient closed fiber is, provided its source is coefficient-flat. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R A C : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing C]
variable [Algebra R A] [IsLocalHom (algebraMap R A)]
variable [Algebra R C] [Algebra A C] [IsScalarTower R A C]
variable [Module.Finite A C] [Module.Flat R C]

theorem affineLocal_isIso_of_closedFiber
    (h : IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))))) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
  let φ : A →ₐ[R] C := IsScalarTower.toAlgHom R A C
  have ht : Function.Bijective (((Algebra.linearMap A C).restrictScalars R).lTensor
      (IsLocalRing.ResidueField R)) :=
    (RelativeIsomorphismTensorCriterion.affineRelativeBaseChange_isIso_iff_tensor (K := IsLocalRing.ResidueField R) φ).mp h
  exact isIso_SpecMap_iff.mpr (Local.CoefficientFiberIsomorphism.localAlgebra_bijective_of_closedFiber ht)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.LocalClosedFiberIsomorphism
