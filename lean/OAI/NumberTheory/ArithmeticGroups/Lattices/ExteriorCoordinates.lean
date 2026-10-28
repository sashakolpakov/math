import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedMonomialBasis
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorRepresentation

/-! # Exterior Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorCoordinates.Construction

noncomputable section

/-! Uniform finite coordinates for the exterior representation. In these
coordinates scalar extension is coefficientwise extension of scalars. -/

open scoped Classical

abbrev BoundedExteriorIndices (n d r : ℕ) :=
  Set.powersetCard (Fin (BoundedMonomialBasis.Construction.boundedMonomialCount n d)) r

def boundedExteriorBasis (k : Type) [Field k] (n d r : ℕ) :
    Module.Basis (BoundedExteriorIndices n d r) k (⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)) :=
  (BoundedMonomialBasis.Construction.boundedMonomialBasis k n d).exteriorPower r

def boundedExteriorCoordinates (k : Type) [Field k] (n d r : ℕ) :
    (⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)) ≃ₗ[k] (BoundedExteriorIndices n d r → k) :=
  (boundedExteriorBasis k n d r).equivFun

theorem boundedExteriorCoordinates_wedge
    {k : Type} [Field k] {n d r : ℕ} (p : Fin r → BoundedRepresentation.Construction.BoundedPolynomials k n d)
    (s : BoundedExteriorIndices n d r) :
    boundedExteriorCoordinates k n d r (exteriorPower.ιMulti k r p) s =
      (Matrix.of (fun i j => (BoundedMonomialBasis.Construction.boundedMonomialBasis k n d).repr (p i)
        (Set.powersetCard.ofFinEmbEquiv.symm s j))).det := by
  change ((BoundedMonomialBasis.Construction.boundedMonomialBasis k n d).exteriorPower r).repr
    (exteriorPower.ιMulti k r p) s = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

theorem boundedExteriorCoordinates_wedge_coefficient_map
    {k K : Type} [Field k] [Field K] [Algebra k K] {n d r : ℕ}
    (p : Fin r → BoundedRepresentation.Construction.BoundedPolynomials k n d) (s : BoundedExteriorIndices n d r) :
    boundedExteriorCoordinates K n d r
        (exteriorPower.ιMulti K r (fun i => Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (p i))) s =
      algebraMap k K (boundedExteriorCoordinates k n d r (exteriorPower.ιMulti k r p) s) := by
  rw [boundedExteriorCoordinates_wedge, boundedExteriorCoordinates_wedge, RingHom.map_det]
  congr 1

def boundedExteriorCoefficientMap
    {k K : Type} [Field k] [Field K] [Algebra k K] (n d r : ℕ) :
    (⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)) →ₗ[k] (⋀[K]^r (BoundedRepresentation.Construction.BoundedPolynomials K n d)) :=
  ((boundedExteriorCoordinates K n d r).symm.toLinearMap.restrictScalars k).comp
    ((LinearMap.pi (fun i => (Algebra.linearMap k K).comp (LinearMap.proj i))).comp
      (boundedExteriorCoordinates k n d r).toLinearMap)

theorem boundedExteriorCoefficientMap_wedge
    {k K : Type} [Field k] [Field K] [Algebra k K] {n d r : ℕ}
    (p : Fin r → BoundedRepresentation.Construction.BoundedPolynomials k n d) :
    boundedExteriorCoefficientMap (K := K) n d r (exteriorPower.ιMulti k r p) =
      exteriorPower.ιMulti K r (fun i => Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (p i)) := by
  apply (boundedExteriorCoordinates K n d r).injective
  ext s
  change boundedExteriorCoordinates K n d r
    ((boundedExteriorCoordinates K n d r).symm
      (fun i => algebraMap k K
        (boundedExteriorCoordinates k n d r (exteriorPower.ιMulti k r p) i))) s = _
  rw [LinearEquiv.apply_symm_apply, boundedExteriorCoordinates_wedge_coefficient_map]

theorem boundedExteriorCoefficientMap_injective
    {k K : Type} [Field k] [Field K] [Algebra k K] (n d r : ℕ) :
    Function.Injective (boundedExteriorCoefficientMap (k := k) (K := K) n d r) := by
  intro x y h
  apply (boundedExteriorCoordinates k n d r).injective
  ext s
  apply (algebraMap k K).injective
  have he := congrArg (fun w => boundedExteriorCoordinates K n d r w s) h
  simpa only [boundedExteriorCoefficientMap, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.pi_apply, LinearMap.proj_apply, Algebra.linearMap_apply] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorCoordinates.Construction
