import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ExtendedQuotient
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced

/-! # Dual Frame Center Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DualFrameCenterSmooth.Construction

noncomputable section

/-! A center cut out by a dual coordinate family is smooth and reduced over the original field. -/

universe u

section Smooth

variable {k A ι : Type u} [CommRing k] [CommRing A] [Algebra k A]

theorem idealOfVars_map_aeval (z : ι → A) :
    (MvPolynomial.idealOfVars ι k).map (MvPolynomial.aeval z).toRingHom = Ideal.span (Set.range z) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact MvPolynomial.aeval_X z i

variable [Fintype ι] [DecidableEq ι]

theorem smooth_coordinate_center_quotient [Algebra (MvPolynomial ι k) A]
    [IsScalarTower k (MvPolynomial ι k) A] [Algebra.Smooth (MvPolynomial ι k) A] :
    Algebra.Smooth k (A ⧸ (MvPolynomial.idealOfVars ι k).map (algebraMap (MvPolynomial ι k) A)) := by
  have he : SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) (Finset.univ : Finset ι) = MvPolynomial.idealOfVars ι k := by
    rw [SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal, Finset.coe_univ, Set.image_univ]
  let : Algebra.Smooth k (MvPolynomial ι k ⧸ MvPolynomial.idealOfVars ι k) :=
    he ▸ Blowups.Smooth.SubsetCenter.Construction.subsetCoordinateCenter_smooth (R := k) (Finset.univ : Finset ι)
  exact Blowups.Smooth.ExtendedQuotient.Construction.smooth_extended_quotient (MvPolynomial.idealOfVars ι k)

/-- A finite family with dual derivations defines an actual smooth closed
center inside any smooth affine algebra over the base. -/
theorem dual_derivation_family_center_smooth [Algebra.Smooth k A]
    (z : ι → A) (D : ι → Derivation k A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) :
    Algebra.Smooth k (A ⧸ Ideal.span (Set.range z)) := by
  let φ : MvPolynomial ι k →ₐ[k] A := MvPolynomial.aeval z
  let : Algebra (MvPolynomial ι k) A := φ.toRingHom.toAlgebra
  let : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have hframe : ∀ i j, D i (algebraMap (MvPolynomial ι k) A (MvPolynomial.X j)) =
      if i = j then 1 else 0 := by
    intro i j
    change D i ((MvPolynomial.aeval (R := k) z) (MvPolynomial.X j)) = _
    rw [MvPolynomial.aeval_X]
    exact hD i j
  let : Algebra.Smooth (MvPolynomial ι k) A := Blowups.Smooth.CoordinateFrame.Construction.smooth_over_coordinate_frame D hframe
  have h := smooth_coordinate_center_quotient (k := k) (A := A) (ι := ι)
  change Algebra.Smooth k (A ⧸ (MvPolynomial.idealOfVars ι k).map (MvPolynomial.aeval z).toRingHom) at h
  rwa [idealOfVars_map_aeval] at h

end Smooth

variable {k A ι : Type u} [Field k] [IsAlgClosed k] [CommRing A]
  [Algebra k A] [Algebra.Smooth k A] [Fintype ι] [DecidableEq ι]

/-- The actual dual-coordinate center ideal is radical over an algebraically closed field. -/
theorem dual_derivation_family_center_isRadical (z : ι → A) (D : ι → Derivation k A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) :
    (Ideal.span (Set.range z)).IsRadical := by
  let : Algebra.Smooth k (A ⧸ Ideal.span (Set.range z)) :=
    dual_derivation_family_center_smooth z D hD
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr (Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DualFrameCenterSmooth.Construction
