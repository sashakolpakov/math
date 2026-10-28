import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverlapTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyTransport

/-! # Family Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyBaseChange

noncomputable section

/-! Base change of the actual stable-Hilbert chart families and their
canonical transport, on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

section Generic
variable {S : Scheme.{u}} {W A B Z T U : Over S}
variable {l : W ⟶ A} {r : W ⟶ B} {p : A ⟶ Z} {q : B ⟶ Z}
variable (H : IsPullback l r p q) (F : Over A.left) (G : Over B.left)
variable (e : (Over.pullback l.left).obj F ≅ (Over.pullback r.left).obj G)
variable (a : T ⟶ A) (b : T ⟶ B) (h : a ≫ p = b ≫ q)

private theorem chartTransport_eq_cartesian
    (c : T ⟶ W) (hl : c ≫ l = a) (hr : c ≫ r = b) :
    FamilyTransport.chartFamilyPullbackTransport H F G e a b h =
      Cartesian.OverlapTransport.cartesianOverlapPullbackIso F G l.left r.left e c.left a.left b.left
        (congrArg Over.Hom.left hl) (congrArg Over.Hom.left hr) := by
  have hc : c = H.lift a b h := by
    apply H.hom_ext
    · exact hl.trans (H.lift_fst a b h).symm
    · exact hr.trans (H.lift_snd a b h).symm
  subst c
  let ca : Over.mk a.left ⟶ Over.mk l.left :=
    Over.homMk (H.lift a b h).left (congrArg Over.Hom.left hl)
  let cb : Over.mk b.left ⟶ Over.mk r.left :=
    Over.homMk (H.lift a b h).left (congrArg Over.Hom.left hr)
  change
    (HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso ca F ≪≫ (Over.pullback (H.lift a b h).left).mapIso e ≪≫
      (HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso cb G).symm) =
    (Single.ParameterBaseChange.singleParameterBaseChangeIso ca F ≪≫ (Over.pullback (H.lift a b h).left).mapIso e ≪≫
      (Single.ParameterBaseChange.singleParameterBaseChangeIso cb G).symm)
  rw [ParameterPullbackIsoComparison.overBaseMapPullbackIso_eq_singleParameter, ParameterPullbackIsoComparison.overBaseMapPullbackIso_eq_singleParameter]

variable (u : U ⟶ T) (hu : (u ≫ a) ≫ p = (u ≫ b) ≫ q)

private theorem chartTransport_baseChange :
    FamilyTransport.chartFamilyPullbackTransport H F G e (u ≫ a) (u ≫ b) hu =
      Single.ParameterBaseChange.singleParameterBaseChangeIso
        (Over.homMk u.left rfl : Over.mk (u ≫ a).left ⟶ Over.mk a.left) F ≪≫
      (Over.pullback u.left).mapIso (FamilyTransport.chartFamilyPullbackTransport H F G e a b h) ≪≫
      (Single.ParameterBaseChange.singleParameterBaseChangeIso
        (Over.homMk u.left rfl : Over.mk (u ≫ b).left ⟶ Over.mk b.left) G).symm := by
  let c := H.lift a b h
  have hl : c ≫ l = a := H.lift_fst a b h
  have hr : c ≫ r = b := H.lift_snd a b h
  have hl' : (u ≫ c) ≫ l = u ≫ a := by rw [Category.assoc, hl]
  have hr' : (u ≫ c) ≫ r = u ≫ b := by rw [Category.assoc, hr]
  rw [chartTransport_eq_cartesian H F G e (u ≫ a) (u ≫ b) hu (u ≫ c) hl' hr',
    chartTransport_eq_cartesian H F G e a b h c hl hr]
  exact Cartesian.OverlapTransport.cartesianOverlapPullbackIso_baseChange F G l.left r.left e
    c.left a.left b.left (congrArg Over.Hom.left hl) (congrArg Over.Hom.left hr)
    u.left (congrArg Over.Hom.left hl') (congrArg Over.Hom.left hr')

private theorem chartTransport_natural :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u.left rfl : Over.mk (u ≫ a).left ⟶ Over.mk a.left) F ≫
        (FamilyTransport.chartFamilyPullbackTransport H F G e a b h).hom.left =
      (FamilyTransport.chartFamilyPullbackTransport H F G e (u ≫ a) (u ≫ b) hu).hom.left ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap
          (Over.homMk u.left rfl : Over.mk (u ≫ b).left ⟶ Over.mk b.left) G := by
  let c := H.lift a b h
  have hl : c ≫ l = a := H.lift_fst a b h
  have hr : c ≫ r = b := H.lift_snd a b h
  have hl' : (u ≫ c) ≫ l = u ≫ a := by rw [Category.assoc, hl]
  have hr' : (u ≫ c) ≫ r = u ≫ b := by rw [Category.assoc, hr]
  rw [chartTransport_eq_cartesian H F G e a b h c hl hr,
    chartTransport_eq_cartesian H F G e (u ≫ a) (u ≫ b) hu (u ≫ c) hl' hr']
  exact Cartesian.OverlapTransport.cartesianOverlapPullbackIso_natural F G l.left r.left e
    c.left a.left b.left (congrArg Over.Hom.left hl) (congrArg Over.Hom.left hr)
    u.left (congrArg Over.Hom.left hl') (congrArg Over.Hom.left hr')
end Generic

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)

def stableHilbertFamilyBaseChangeIso
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T U : Over (Spec (.of R))}
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) (u : U ⟶ T) :
    (Over.pullback (u ≫ a).left).obj (FamilyPullbacks.stableHilbertChartFamily R i D P j) ≅
      (Over.pullback u.left).obj
        ((Over.pullback a.left).obj (FamilyPullbacks.stableHilbertChartFamily R i D P j)) :=
  Single.ParameterBaseChange.singleParameterBaseChangeIso
    (Over.homMk u.left rfl : Over.mk (u ≫ a).left ⟶ Over.mk a.left)
    (FamilyPullbacks.stableHilbertChartFamily R i D P j)

variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable {T : Over (Spec (.of R))}
variable (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
variable (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
variable (h : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
  b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)

theorem stableHilbertFamilyTransport_eq_cartesian
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
    (hl : c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD = a)
    (hr : c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD = b) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b h =
      Cartesian.OverlapTransport.cartesianOverlapPullbackIso
        (FamilyPullbacks.stableHilbertChartFamily R i D P j) (FamilyPullbacks.stableHilbertChartFamily R i D P k)
        (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD).left
        (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD).left
        (FamilyPullbacks.stableHilbertOverlapFamilyIso R i D P hP hD j k)
        c.left a.left b.left (congrArg Over.Hom.left hl) (congrArg Over.Hom.left hr) :=
  chartTransport_eq_cartesian (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D P hP hD)
    (FamilyPullbacks.stableHilbertChartFamily R i D P j) (FamilyPullbacks.stableHilbertChartFamily R i D P k)
    (FamilyPullbacks.stableHilbertOverlapFamilyIso R i D P hP hD j k) a b h c hl hr

variable {U : Over (Spec (.of R))} (u : U ⟶ T)
variable (hu : (u ≫ a) ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
  (u ≫ b) ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)

theorem stableHilbertFamilyTransport_baseChange :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k (u ≫ a) (u ≫ b) hu =
      stableHilbertFamilyBaseChangeIso R i D P j a u ≪≫
        (Over.pullback u.left).mapIso
          (FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b h) ≪≫
        (stableHilbertFamilyBaseChangeIso R i D P k b u).symm :=
  chartTransport_baseChange (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D P hP hD)
    (FamilyPullbacks.stableHilbertChartFamily R i D P j) (FamilyPullbacks.stableHilbertChartFamily R i D P k)
    (FamilyPullbacks.stableHilbertOverlapFamilyIso R i D P hP hD j k) a b h u hu

@[reassoc]
theorem stableHilbertFamilyTransport_natural :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u.left rfl : Over.mk (u ≫ a).left ⟶ Over.mk a.left)
        (FamilyPullbacks.stableHilbertChartFamily R i D P j) ≫
        (FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b h).hom.left =
      (FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k (u ≫ a) (u ≫ b) hu).hom.left ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap
          (Over.homMk u.left rfl : Over.mk (u ≫ b).left ⟶ Over.mk b.left)
          (FamilyPullbacks.stableHilbertChartFamily R i D P k) :=
  chartTransport_natural (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D P hP hD)
    (FamilyPullbacks.stableHilbertChartFamily R i D P j) (FamilyPullbacks.stableHilbertChartFamily R i D P k)
    (FamilyPullbacks.stableHilbertOverlapFamilyIso R i D P hP hD j k) a b h u hu

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyBaseChange
