import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapCriterion

/-! # Polarization Transition Bases -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases

noncomputable section

/-! Native bases and equations for the original polarization transition pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem pullback_left_equation
    {C : Type*} [Category* C] {X Y Z T : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (x : T ⟶ pullback f g) :
    (x ≫ pullback.fst f g) ≫ f = (x ≫ pullback.snd f g) ≫ g :=
  (Category.assoc _ _ _).trans ((congrArg (fun a => x ≫ a)
    (pullback.condition (f := f) (g := g))).trans (Category.assoc _ _ _).symm)

private theorem pullback_right_equation
    {C : Type*} [Category* C] {X Y X' Z Z' T : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y ⟶ Z')
    [HasPullback f g] [HasPullback f' g']
    (e : pullback f g ⟶ pullback f' g')
    (he : e ≫ pullback.snd f' g' = pullback.snd f g)
    (x : T ⟶ pullback f g) :
    (x ≫ (e ≫ pullback.fst f' g')) ≫ f' = (x ≫ pullback.snd f g) ≫ g' := by
  rw [Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc e, he]
  simp only [Category.assoc]

private theorem overPullback_locallyNoetherian_of_finiteType
    {S : Scheme} {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyOfFiniteType f.left] [IsLocallyNoetherian Y.left] :
    IsLocallyNoetherian (pullback f g).left := by
  let : LocallyOfFiniteType ((Over.forget S).map f) := inferInstanceAs (LocallyOfFiniteType f.left)
  let : LocallyOfFiniteType (pullback.snd f g).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      ((IsPullback.of_hasPullback f g).map (Over.forget S)) inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g).left

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

local notation "ij" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels
local notation "ik" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels
local notation "lj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD
local notation "lk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD
def leftBaseMap : pullback ij lj ⟶
    LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels :=
  pullback.fst ij lj

local notation "uL" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k
def rightBaseMap : pullback ij lj ⟶
    LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels :=
  LevelTransitions.StableHilbertFullLevelTransition.forward R i D H hH hD g Hm Hi N labels j k ≫
    pullback.fst ik lk

local notation "uR" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k
local notation "b₀" => pullback.snd ij lj
local notation "O" => pullback ij lj
local notation "pj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "pk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ

def leftParameter : Over (Spec (.of R)) := pullback pj uL

def rightParameter : Over (Spec (.of R)) := pullback pk uR

theorem left_equation {T : Over (Spec (.of R))} (x : T ⟶ O) :
    (x ≫ uL) ≫ ij = (x ≫ b₀) ≫ lj :=
  pullback_left_equation ij lj x

theorem right_equation {T : Over (Spec (.of R))} (x : T ⟶ O) :
    (x ≫ uR) ≫ ik = (x ≫ b₀) ≫ lk :=
  pullback_right_equation ij lj ik lk
    (LevelTransitions.StableHilbertFullLevelTransition.forward R i D H hH hD g Hm Hi N labels j k)
    (LevelTransitions.StableHilbertFullLevelTransition.forward_base R i D H hH hD g Hm Hi N labels j k) x

instance leftParameter_locallyNoetherian :
    IsLocallyNoetherian (leftParameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).left := by
  let : IsLocallyNoetherian (O).left :=
    LevelTransitions.StableHilbertFullLevelTransition.leftParameter_locallyNoetherian R i D H hH hD g Hm Hi N labels j k
  exact overPullback_locallyNoetherian_of_finiteType pj uL

instance rightParameter_locallyNoetherian :
    IsLocallyNoetherian (rightParameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).left := by
  let : IsLocallyNoetherian (O).left :=
    LevelTransitions.StableHilbertFullLevelTransition.leftParameter_locallyNoetherian R i D H hH hD g Hm Hi N labels j k
  exact overPullback_locallyNoetherian_of_finiteType pk uR

end StableHilbertPolarizationTransition

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases
