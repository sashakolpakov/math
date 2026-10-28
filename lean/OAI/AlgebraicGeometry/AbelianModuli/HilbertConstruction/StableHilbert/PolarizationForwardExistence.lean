import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases

/-! # Polarization Forward Existence -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationForwardExistence.StableHilbertPolarizationTransition

/-! The actual two normalized-polarization lifts on the native overlap bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)

local notation "ij" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels
local notation "ik" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels
local notation "lj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD
local notation "lk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD
local notation "uL" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k
local notation "uR" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k
local notation "b₀" => pullback.snd ij lj
local notation "O" => pullback ij lj
local notation "pj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "pk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ

theorem lifts_iff_overBase
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left] (x : T ⟶ O) :
    (∃ a : T ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ,
      a ≫ pj = x ≫ uL) ↔
    (∃ a : T ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i k D H hH g Hm Hi N labels qR d hd δ hδ,
      a ≫ pk = x ≫ uR) :=
  PolarizationOverlapCriterion.StableHilbertPolarization.overlap_lifts_iff R i D H hH hD g Hm Hi N labels
    qR d hd δ hδ j k (x ≫ b₀) (x ≫ uL)
    (PolarizationTransitionBases.StableHilbertPolarizationTransition.left_equation R i D H hH hD g Hm Hi N labels j k x) (x ≫ uR)
    (PolarizationTransitionBases.StableHilbertPolarizationTransition.right_equation R i D H hH hD g Hm Hi N labels j k x)

theorem rightLift :
    ∃ a : pullback pj uL ⟶
        PolarizationParameter.StableHilbertPolarization.parameter R i k D H hH g Hm Hi N labels qR d hd δ hδ,
      a ≫ pk = pullback.snd pj uL ≫ uR := by
  let : IsLocallyNoetherian (pullback pj uL).left :=
    PolarizationTransitionBases.StableHilbertPolarizationTransition.leftParameter_locallyNoetherian R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k
  exact (lifts_iff_overBase R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k
    (pullback.snd pj uL)).mp ⟨pullback.fst pj uL, pullback.condition⟩

theorem leftLift :
    ∃ a : pullback pk uR ⟶
        PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ,
      a ≫ pj = pullback.snd pk uR ≫ uL := by
  let : IsLocallyNoetherian (pullback pk uR).left :=
    PolarizationTransitionBases.StableHilbertPolarizationTransition.rightParameter_locallyNoetherian R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k
  exact (lifts_iff_overBase R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k
    (pullback.snd pk uR)).mpr ⟨pullback.fst pk uR, pullback.condition⟩

end AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationForwardExistence.StableHilbertPolarizationTransition

namespace AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationForwardExistence

/-! The original forward lift first supplies its map as an existential
witness. The projection determines this map uniquely. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem exists_map_to_pullback_over
    {C : Type*} [Category* C] {T X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (b : T ⟶ Y)
    (h : ∃ a : T ⟶ X, a ≫ f = b ≫ g) :
    ∃ e : T ⟶ pullback f g, e ≫ pullback.snd f g = b := by
  obtain ⟨a, ha⟩ := h
  exact ⟨pullback.lift a b ha, pullback.lift_snd _ _ _⟩

namespace StableHilbertPolarizationTransition
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)

theorem exists_forward_over :
    ∃ e : pullback (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)
        (PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k) ⟶
      pullback (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)
        (PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k),
      e ≫ pullback.snd (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)
          (PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k) =
        pullback.snd (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)
          (PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k) :=
  exists_map_to_pullback_over
    (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)
    (PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k)
    (pullback.snd (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)
      (PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k))
    (rightLift R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

def forwardOfExists := (exists_forward_over R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose

theorem forwardOfExists_base :
    forwardOfExists R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k ≫
      pullback.snd (PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ)
        (PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k) =
      pullback.snd (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)
        (PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k) :=
  (exists_forward_over R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose_spec

end StableHilbertPolarizationTransition

end AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationForwardExistence

end

end OAI
