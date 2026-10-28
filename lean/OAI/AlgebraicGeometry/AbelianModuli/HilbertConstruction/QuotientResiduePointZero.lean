import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointRationalZero

/-! # Quotient Residue Point Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuotientResiduePointZero

noncomputable section

/-! A closed one-point quotient of the spectrum of a local ring lies over its closed point. For an actual stalk at a rational section, every residue point of this quotient is therefore the rational zero section over its actual base map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem closedImmersion_singlePoint_localSpec_image
    {R : Type u} [CommRing R] [IsLocalRing R] {T : Scheme.{u}} [Subsingleton T]
    (j : T ⟶ Spec (.of R)) [IsClosedImmersion j] (x : T) :
    j x = IsLocalRing.closedPoint R := by
  have hc : IsClosed (Set.range j) := j.isClosedEmbedding.isClosed_range
  obtain ⟨y, hy⟩ := (IsLocalRing.specializes_closedPoint (j x)).mem_closed hc ⟨x, rfl⟩
  exact (congrArg j (Subsingleton.elim x y)).trans hy

theorem affine_stalk_quotient_residue_point_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (I : Ideal Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤))
    [Subsingleton (Spec (.of (Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤) ⧸ I)))] :
    let T := Spec (.of (Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤) ⧸ I));
    let j : T ⟶ X :=
      (Affine.QuotientCoefficientMap.affineCoordinateMap (S := Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))))
        (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk (z (IsLocalRing.closedPoint K));
    ∀ x : T, T.fromSpecResidueField x ≫ j = ((T.fromSpecResidueField x ≫ j) ≫ p) ≫ z := by
  let x₀ := z (IsLocalRing.closedPoint K)
  let O := X.presheaf.stalk x₀
  have hO : IsLocalRing (↑O) := X.toLocallyRingedSpace.isLocalRing x₀
  let T := Spec (.of (Γ(Spec O, ⊤) ⧸ I))
  let j : T ⟶ Spec O := Affine.QuotientCoefficientMap.affineCoordinateMap (Ideal.Quotient.mk I)
  have : IsClosedImmersion j := Affine.QuotientCoefficientMap.affineCoordinateMap_isClosedImmersion
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  change ∀ x : T, T.fromSpecResidueField x ≫ (j ≫ X.fromSpecStalk x₀) =
    ((T.fromSpecResidueField x ≫ (j ≫ X.fromSpecStalk x₀)) ≫ p) ≫ z
  intro x
  let t : Spec (T.residueField x) ⟶ X := T.fromSpecResidueField x ≫ (j ≫ X.fromSpecStalk x₀)
  have hj : j x = @IsLocalRing.closedPoint O inferInstance hO :=
    @closedImmersion_singlePoint_localSpec_image O inferInstance hO T inferInstance j inferInstance x
  have hpoint : t (IsLocalRing.closedPoint (T.residueField x)) = x₀ := by
    change X.fromSpecStalk x₀ (j (T.fromSpecResidueField x _)) = x₀
    exact (congrArg (fun y : T => X.fromSpecStalk x₀ (j y))
      (Scheme.fromSpecResidueField_apply x _)).trans
        ((congrArg (X.fromSpecStalk x₀) hj).trans Scheme.fromSpecStalk_closedPoint)
  exact HilbertConstruction.Field.PointRationalZero.fieldPoint_eq_rational_section_of_point p z hz t hpoint

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuotientResiduePointZero
