import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointStalkRegularParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceProjectiveDimension
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Point Residue Projective Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidueProjectiveDimension

noncomputable section

/-! At a rational smooth point, the residue field has projective dimension equal to the geometric relative dimension. This uses the constructed regular parameters in the actual stalk. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry IsLocalRing
universe u

theorem residue_projectiveDimension_of_regular_parameters
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs) (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R) :
    Projective.DimensionBasic.projectiveDimension (ModuleCat.of.{u} R (ResidueField R)) = (rs.length : WithBot ℕ∞) := by
  have hdim : Projective.DimensionBasic.projectiveDimension (ModuleCat.of.{u} R (Shrink.{u} (R ⧸ Regular.SequenceBasic.Ideal.ofList rs))) =
      (rs.length : WithBot ℕ∞) :=
    Regular.SequenceProjectiveDimension.ModuleCat.projectiveDimension_quotient_eq_length rs hreg
  rw [hgen] at hdim
  let e : ModuleCat.of.{u} R (Shrink.{u} (R ⧸ maximalIdeal R)) ≅
      ModuleCat.of.{u} R (ResidueField R) := (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).toModuleIso
  exact (Projective.DimensionBasic.projectiveDimension_eq_of_iso e).symm.trans hdim

theorem rationalPoint_residue_projectiveDimension
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (g : ℕ) [SmoothOfRelativeDimension g p]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    Projective.DimensionBasic.projectiveDimension (ModuleCat.of.{u}
      (X.presheaf.stalk (s (IsLocalRing.closedPoint K)))
      (ResidueField (X.presheaf.stalk (s (IsLocalRing.closedPoint K))))) = (g : WithBot ℕ∞) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth g p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let x := s (IsLocalRing.closedPoint K)
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
      (X := X) (x := x)
  obtain ⟨rs, hreg, hgen, hlen⟩ := PointStalkRegularParameters.rationalPoint_stalk_regular_parameters p g s hs
  rw [← hlen]
  exact residue_projectiveDimension_of_regular_parameters (X.presheaf.stalk x) rs hreg hgen

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidueProjectiveDimension
