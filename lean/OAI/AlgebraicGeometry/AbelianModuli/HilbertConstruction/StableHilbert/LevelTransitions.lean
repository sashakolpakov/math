import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineMarkedTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ChartPullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.AffineCoverLifts

/-! # Level Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitions

noncomputable section

/-! Actual transition isomorphisms between the marked full-level
parameter pullbacks on a stable Hilbert overlap. Affine transition
existence comes from the native family isomorphism and its coordinate
and marked-point identities; monomorphy glues the unique lifts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem uniqueLift_iff_lift {S : Scheme.{u}} {X Y T : Over S}
    (i : X ⟶ Y) [Mono i] (c : T ⟶ Y) :
    (∃! a : T ⟶ X, a ≫ i = c) ↔ (∃ a : T ⟶ X, a ≫ i = c) := by
  constructor
  · exact ExistsUnique.exists
  · rintro ⟨a, ha⟩
    exact ⟨a, ha, fun b hb => (cancel_mono i).mp (hb.trans ha.symm)⟩

private structure PullbackLiftData
    {C : Type*} [Category* C] {T X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (b : T ⟶ Y) where
  hom : T ⟶ pullback f g
  hom_snd : hom ≫ pullback.snd f g = b

private def pullbackLiftOfUnique
    {C : Type*} [Category* C] {T X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (b : T ⟶ Y)
    (h : ∃! a : T ⟶ X, a ≫ f = b ≫ g) : PullbackLiftData f g b where
  hom := pullback.lift h.choose b h.choose_spec.1
  hom_snd := pullback.lift_snd _ _ _

private theorem comp_eq_id_of_base
    {C : Type*} [Category* C] {X Y Z : C}
    (p : X ⟶ Z) [Mono p] (q : Y ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : f ≫ q = p) (hg : g ≫ p = q) : f ≫ g = 𝟙 X :=
  (cancel_mono p).mp ((Category.assoc _ _ _).trans
    ((congrArg (fun h => f ≫ h) hg).trans (hf.trans (Category.id_comp p).symm)))

private def pullbackLiftDataIso
    {C : Type*} [Category* C] {X Y I J K : C}
    (i : X ⟶ I) (j : Y ⟶ J) (l : K ⟶ I) (r : K ⟶ J)
    [HasPullback i l] [HasPullback j r] [Mono i] [Mono j]
    (F : PullbackLiftData j r (pullback.snd i l))
    (G : PullbackLiftData i l (pullback.snd j r)) : pullback i l ≅ pullback j r where
  hom := F.hom
  inv := G.hom
  hom_inv_id := comp_eq_id_of_base (pullback.snd i l) (pullback.snd j r)
    F.hom G.hom F.hom_snd G.hom_snd
  inv_hom_id := comp_eq_id_of_base (pullback.snd j r) (pullback.snd i l)
    G.hom F.hom G.hom_snd F.hom_snd

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

include hD in
private theorem affineFullLevelLift_transport
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) {f : Spec (.of C) ⟶ Spec (.of R)}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (ha : ∃ u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels = a) :
    ∃ u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels = b := by
  obtain ⟨c, hca, hcb⟩ :=
    (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D H hH hD).exists_lift a b hab
  have hca' : ∃ u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels =
        c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD := by
    obtain ⟨u, hu⟩ := ha
    exact ⟨u, hu.trans hca.symm⟩
  obtain ⟨v, hv⟩ := AffineMarkedTransport.stableHilbertFullLevel_overlap_hasPoint R i j D H hH hD k c g Hm Hi N labels hca'
  exact ⟨v, hv.trans hcb⟩

include hD in
theorem stableHilbertFullLevel_affine_lift_iff
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) {f : Spec (.of C) ⟶ Spec (.of R)}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H) :
    (∃ u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels = a) ↔
    (∃ u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels = b) :=
  ⟨affineFullLevelLift_transport R i D H hH hD g Hm Hi N labels j k a b hab,
    affineFullLevelLift_transport R i D H hH hD g Hm Hi N labels k j b a hab.symm⟩

include hD in
theorem stableHilbertFullLevel_noetherian_lift_iff
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H) :
    (∃! u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels = a) ↔
    (∃! u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels = b) := by
  rw [HilbertConstruction.Over.AffineCoverLifts.overUniqueLift_iff_affineOpenCover, HilbertConstruction.Over.AffineCoverLifts.overUniqueLift_iff_affineOpenCover]
  apply forall_congr'
  intro z
  have hC : IsNoetherianRing (T.left.affineOpenCover.X z) := isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (T.left.affineOpenCover.f z))
  rw [uniqueLift_iff_lift, uniqueLift_iff_lift]
  have hab' : (HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T z ≫ a) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T z ≫ b) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T z ≫ q) hab).trans (Category.assoc _ _ _).symm)
  exact @stableHilbertFullLevel_affine_lift_iff R _ _ n m i D H hH hD g Hm Hi N _ labels
    (T.left.affineOpenCover.X z) _ hC j k (T.left.affineOpenCover.f z ≫ T.hom)
    (HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T z ≫ a) (HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T z ≫ b) hab'

namespace StableHilbertFullLevelTransition
variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

local notation "Mj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels
local notation "Mk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels
local notation "ij" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels
local notation "ik" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels
local notation "lj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD
local notation "lk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD

def leftParameter : Over (Spec (.of R)) := pullback ij lj

def rightParameter : Over (Spec (.of R)) := pullback ik lk

instance leftParameter_locallyNoetherian :
    IsLocallyNoetherian (leftParameter R i D H hH hD g Hm Hi N labels j k).left :=
  NoetherianCharts.overPullback_locallyNoetherian_of_open ij lj

instance rightParameter_locallyNoetherian :
    IsLocallyNoetherian (rightParameter R i D H hH hD g Hm Hi N labels j k).left :=
  NoetherianCharts.overPullback_locallyNoetherian_of_open ik lk

private theorem left_to_right_lift :
    ∃! u : pullback ij lj ⟶ Mk,
      u ≫ ik = pullback.snd ij lj ≫ lk := by
  let : IsLocallyNoetherian (pullback ij lj).left := NoetherianCharts.overPullback_locallyNoetherian_of_open ij lj
  have hab : (pullback.fst ij lj ≫ ij) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (pullback.snd ij lj ≫ lk) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H := by
    rw [pullback.condition, Category.assoc, Category.assoc,
      ChartPullbacks.stableHilbertIntersectionLeftMap_toRank, ChartPullbacks.stableHilbertIntersectionRightMap_toRank]
  apply (stableHilbertFullLevel_noetherian_lift_iff R i D H hH hD g Hm Hi N labels j k
    (pullback.fst ij lj ≫ ij) (pullback.snd ij lj ≫ lk) hab).mp
  exact ⟨pullback.fst ij lj, rfl, fun v hv => (cancel_mono ij).mp hv⟩

private theorem right_to_left_lift :
    ∃! u : pullback ik lk ⟶ Mj,
      u ≫ ij = pullback.snd ik lk ≫ lj := by
  let : IsLocallyNoetherian (pullback ik lk).left := NoetherianCharts.overPullback_locallyNoetherian_of_open ik lk
  have hab : (pullback.snd ik lk ≫ lj) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (pullback.fst ik lk ≫ ik) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H := by
    rw [pullback.condition, Category.assoc, Category.assoc,
      ChartPullbacks.stableHilbertIntersectionLeftMap_toRank, ChartPullbacks.stableHilbertIntersectionRightMap_toRank]
  apply (stableHilbertFullLevel_noetherian_lift_iff R i D H hH hD g Hm Hi N labels j k
    (pullback.snd ik lk ≫ lj) (pullback.fst ik lk ≫ ik) hab).mpr
  exact ⟨pullback.fst ik lk, rfl, fun v hv => (cancel_mono ik).mp hv⟩

private def forwardData : PullbackLiftData ik lk (pullback.snd ij lj) :=
  pullbackLiftOfUnique ik lk (pullback.snd ij lj) (left_to_right_lift R i D H hH hD g Hm Hi N labels j k)

private def backwardData : PullbackLiftData ij lj (pullback.snd ik lk) :=
  pullbackLiftOfUnique ij lj (pullback.snd ik lk) (right_to_left_lift R i D H hH hD g Hm Hi N labels j k)

def forward : pullback ij lj ⟶ pullback ik lk :=
  (forwardData R i D H hH hD g Hm Hi N labels j k).hom

def backward : rightParameter R i D H hH hD g Hm Hi N labels j k ⟶
    leftParameter R i D H hH hD g Hm Hi N labels j k :=
  (backwardData R i D H hH hD g Hm Hi N labels j k).hom

theorem forward_base :
    forward R i D H hH hD g Hm Hi N labels j k ≫ pullback.snd ik lk = pullback.snd ij lj :=
  (forwardData R i D H hH hD g Hm Hi N labels j k).hom_snd

theorem backward_base :
    backward R i D H hH hD g Hm Hi N labels j k ≫ pullback.snd ij lj = pullback.snd ik lk :=
  (backwardData R i D H hH hD g Hm Hi N labels j k).hom_snd

def iso : leftParameter R i D H hH hD g Hm Hi N labels j k ≅
    rightParameter R i D H hH hD g Hm Hi N labels j k :=
  pullbackLiftDataIso ij ik lj lk (forwardData R i D H hH hD g Hm Hi N labels j k)
    (backwardData R i D H hH hD g Hm Hi N labels j k)

theorem iso_over :
    (iso R i D H hH hD g Hm Hi N labels j k).hom ≫ pullback.snd ik lk = pullback.snd ij lj :=
  (forwardData R i D H hH hD g Hm Hi N labels j k).hom_snd

end StableHilbertFullLevelTransition

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitions
