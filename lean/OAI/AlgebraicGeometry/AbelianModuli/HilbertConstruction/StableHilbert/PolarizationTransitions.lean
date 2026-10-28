import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationForwardIdentity

/-! # Polarization Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitions

noncomputable section

/-! Actual transition isomorphisms between the normalized polarization loci,
constructed from their original pullback lifts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem comp_eq_id_of_base
    {C : Type*} [Category* C] {X Y Z : C}
    (p : X ⟶ Z) [Mono p] (q : Y ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : f ≫ q = p) (hg : g ≫ p = q) : f ≫ g = 𝟙 X :=
  (cancel_mono p).mp ((Category.assoc _ _ _).trans
    ((congrArg (fun h => f ≫ h) hg).trans (hf.trans (Category.id_comp p).symm)))

private def isoOfBaseMaps
    {C : Type*} [Category* C] {X Y Z : C}
    (p : X ⟶ Z) [Mono p] (q : Y ⟶ Z) [Mono q]
    (f : X ⟶ Y) (g : Y ⟶ X) (hf : f ≫ q = p) (hg : g ≫ p = q) : X ≅ Y where
  hom := f
  inv := g
  hom_inv_id := comp_eq_id_of_base p q f g hf hg
  inv_hom_id := comp_eq_id_of_base q p g f hg hf

private def isoFromPullbackBaseMaps
    {C : Type*} [Category* C] {X Y I J K : C}
    (i : X ⟶ I) (j : Y ⟶ J) (l : K ⟶ I) (r : K ⟶ J)
    [HasPullback i l] [HasPullback j r] [Mono i] [Mono j]
    (f : pullback i l ⟶ pullback j r) (g : pullback j r ⟶ pullback i l)
    (hf : f ≫ pullback.snd j r = pullback.snd i l)
    (hg : g ≫ pullback.snd i l = pullback.snd j r) : pullback i l ≅ pullback j r :=
  isoOfBaseMaps (pullback.snd i l) (pullback.snd j r) f g hf hg

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
local notation "uL" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases.StableHilbertPolarizationTransition.leftBaseMap R i D H hH hD g Hm Hi N labels j k
local notation "uR" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitionBases.StableHilbertPolarizationTransition.rightBaseMap R i D H hH hD g Hm Hi N labels j k
local notation "b₀" => pullback.snd ij lj
local notation "O" => pullback ij lj
local notation "pj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "pk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ

def forward : pullback pj uL ⟶ pullback pk uR :=
  PolarizationForwardExistence.StableHilbertPolarizationTransition.forwardOfExists R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k

def backward : pullback pk uR ⟶ pullback pj uL :=
  pullback.lift (PolarizationForwardExistence.StableHilbertPolarizationTransition.leftLift R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose
    (pullback.snd pk uR) (PolarizationForwardExistence.StableHilbertPolarizationTransition.leftLift R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).choose_spec

theorem forward_base :
    forward R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k ≫ pullback.snd pk uR = pullback.snd pj uL :=
  PolarizationForwardExistence.StableHilbertPolarizationTransition.forwardOfExists_base R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k

theorem backward_base :
    backward R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k ≫ pullback.snd pj uL = pullback.snd pk uR :=
  pullback.lift_snd _ _ _

def iso : PolarizationTransitionBases.StableHilbertPolarizationTransition.leftParameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k ≅
    PolarizationTransitionBases.StableHilbertPolarizationTransition.rightParameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k :=
  isoFromPullbackBaseMaps pj pk uL uR
    (forward R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (backward R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (forward_base R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)
    (backward_base R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

theorem iso_over :
    (iso R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).hom ≫ pullback.snd pk uR =
      pullback.snd pj uL := forward_base R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k

end StableHilbertPolarizationTransition

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationTransitions
