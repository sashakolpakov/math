import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialContinuity

/-! # Coordinate Representation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateRepresentation.Construction

noncomputable section

section

/-! The exterior representation in ordinary finite coordinate spaces,
including joint continuity of the group action. -/

open scoped Classical

def transportLinearRepresentation
    {k H V W : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : H →* (V ≃ₗ[k] V)) (e : V ≃ₗ[k] W) :
    H →* (W ≃ₗ[k] W) where
  toFun g := (e.symm.trans (ρ g)).trans e
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

def boundedExteriorCoordinateRepresentation {k : Type} [Field k] {n : ℕ} (d r : ℕ) :
    Algebraic.SL n k →* ((ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k) ≃ₗ[k] (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k)) :=
  transportLinearRepresentation (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r)
    (ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r)

theorem boundedExteriorCoordinateRepresentation_apply
    {k : Type} [Field k] {n d r : ℕ} (g : Algebraic.SL n k) (x : ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k) :
    boundedExteriorCoordinateRepresentation d r g x =
      ∑ t, x t • ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r
        (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r g (ExteriorCoordinates.Construction.boundedExteriorBasis k n d r t)) := by
  change ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r
    (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r g ((ExteriorCoordinates.Construction.boundedExteriorBasis k n d r).equivFun.symm x)) = _
  rw [Module.Basis.equivFun_symm_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul, map_smul]

theorem continuous_boundedExteriorCoordinateRepresentation
    {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] (n d r : ℕ) :
    Continuous (fun a : Algebraic.SL n k × (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k) =>
      boundedExteriorCoordinateRepresentation d r a.1 a.2) := by
  simp_rw [boundedExteriorCoordinateRepresentation_apply]
  apply continuous_pi
  intro s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change Continuous (fun a : Algebraic.SL n k × (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k) =>
    ∑ t, a.2 t * ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r
      (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r a.1 (ExteriorCoordinates.Construction.boundedExteriorBasis k n d r t)) s)
  apply continuous_finsetSum
  intro t _
  exact ((continuous_apply t).comp continuous_snd).mul
    ((PolynomialContinuity.Construction.continuous_boundedExterior_basis_coordinate s t).comp continuous_fst)

theorem boundedExteriorCoordinates_action
    {k : Type} [Field k] {n d r : ℕ} (g : Algebraic.SL n k) (w : ⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)) :
    boundedExteriorCoordinateRepresentation d r g (ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r w) =
      ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r g w) := by
  change ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r
    (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r g
      ((ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r).symm (ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r w))) = _
  rw [LinearEquiv.symm_apply_apply]

end

/-! Scalar extension commutes with the bounded polynomial, exterior,
and finite-coordinate group actions. -/

open scoped Classical

theorem boundedCoefficientMap_action
    {k K : Type} [Field k] [Field K] [Algebra k K] {n d : ℕ}
    (g : Algebraic.SL n k) (p : BoundedRepresentation.Construction.BoundedPolynomials k n d) :
    Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g p) =
      BoundedRepresentation.Construction.boundedPolynomialRepresentation d (Matrix.SpecialLinearGroup.map (algebraMap k K) g)
        (Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) p) := by
  apply Subtype.ext
  exact Integral.Polynomial.Construction.rightTranslationOverRing_coefficient_map (algebraMap k K)
    (g : Matrix (Fin n) (Fin n) k) p.val

theorem boundedExteriorCoefficientMap_action
    {k K : Type} [Field k] [Field K] [Algebra k K] {n d r : ℕ}
    (g : Algebraic.SL n k) (w : ⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)) :
    ExteriorCoordinates.Construction.boundedExteriorCoefficientMap (K := K) n d r (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r g w) =
      ExteriorRepresentation.Construction.boundedExteriorRepresentation d r (Matrix.SpecialLinearGroup.map (algebraMap k K) g)
        (ExteriorCoordinates.Construction.boundedExteriorCoefficientMap (K := K) n d r w) := by
  have he : (ExteriorCoordinates.Construction.boundedExteriorCoefficientMap (K := K) n d r).comp
      (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r g).toLinearMap =
      ((ExteriorRepresentation.Construction.boundedExteriorRepresentation d r
        (Matrix.SpecialLinearGroup.map (algebraMap k K) g)).toLinearMap.restrictScalars k).comp
          (ExteriorCoordinates.Construction.boundedExteriorCoefficientMap (K := K) n d r) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro p
    change ExteriorCoordinates.Construction.boundedExteriorCoefficientMap (K := K) n d r
      (exteriorPower.map r (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g).toLinearMap
        (exteriorPower.ιMulti k r p)) =
      exteriorPower.map r
        (BoundedRepresentation.Construction.boundedPolynomialRepresentation d (Matrix.SpecialLinearGroup.map (algebraMap k K) g)).toLinearMap
        (ExteriorCoordinates.Construction.boundedExteriorCoefficientMap (K := K) n d r (exteriorPower.ιMulti k r p))
    rw [exteriorPower.map_apply_ιMulti, ExteriorCoordinates.Construction.boundedExteriorCoefficientMap_wedge,
      ExteriorCoordinates.Construction.boundedExteriorCoefficientMap_wedge, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact boundedCoefficientMap_action g (p i)
  exact LinearMap.congr_fun he w

theorem boundedExteriorCoordinateRepresentation_scalar_extension
    {k K : Type} [Field k] [Field K] [Algebra k K] {n d r : ℕ}
    (g : Algebraic.SL n k) (x : ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k) :
    boundedExteriorCoordinateRepresentation d r (Matrix.SpecialLinearGroup.map (algebraMap k K) g)
        (fun i => algebraMap k K (x i)) =
      (fun i => algebraMap k K (boundedExteriorCoordinateRepresentation d r g x i)) := by
  let w := (ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r).symm x
  have hw : ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r w = x := LinearEquiv.apply_symm_apply _ x
  have hm (z : ⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)) :
      ExteriorCoordinates.Construction.boundedExteriorCoordinates K n d r (ExteriorCoordinates.Construction.boundedExteriorCoefficientMap (K := K) n d r z) =
        (fun i => algebraMap k K (ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r z i)) := by
    change ExteriorCoordinates.Construction.boundedExteriorCoordinates K n d r
      ((ExteriorCoordinates.Construction.boundedExteriorCoordinates K n d r).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [← hw, ← hm w, boundedExteriorCoordinates_action, ← boundedExteriorCoefficientMap_action,
    hm, ← boundedExteriorCoordinates_action]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateRepresentation.Construction
