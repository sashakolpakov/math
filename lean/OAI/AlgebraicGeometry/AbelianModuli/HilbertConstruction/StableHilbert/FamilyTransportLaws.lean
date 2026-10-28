import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyAffineComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IsoCocycleDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismFactorizationInduction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NoetherianCharts

/-! # Family Transport Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyTransportLaws

noncomputable section

/-! Identity and cocycle laws for the actual stable-Hilbert family
transports, first on affine charts and then on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v w

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IsoCocycleDetection.AffineIsoCocycleDetection

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

private theorem stableHilbertFamilyTransport_affine_self
    (C : Type u) [CommRing C] [IsNoetherianRing C]
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) {f : Spec (.of C) ⟶ Spec (.of R)}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j j a a rfl = Iso.refl _ := by
  apply Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoSelf_of_conjugate (FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) j a)
  exact (FamilyAffineComparison.stableHilbertFamilyTransport_affine R i D P hP hD (.of C) j j a a rfl).trans
    (Affine.ChartTransport.affineHilbertChartFamilyTransport_self R i j D P hP hD (.of C) a)

private theorem stableHilbertFamilyTransport_affine_cocycle
    (C : Type u) [CommRing C] [IsNoetherianRing C]
    (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) {f : Spec (.of C) ⟶ Spec (.of R)}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hac : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b hab ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l b c hbc =
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l a c hac := by
  apply Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoCocycle_of_conjugate (FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) j a)
    (FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) k b) (FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) l c)
  exact Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoCocycle_of_comparisons
    (FamilyAffineComparison.stableHilbertFamilyTransport_affine R i D P hP hD (.of C) j k a b hab)
    (FamilyAffineComparison.stableHilbertFamilyTransport_affine R i D P hP hD (.of C) k l b c hbc)
    (FamilyAffineComparison.stableHilbertFamilyTransport_affine R i D P hP hD (.of C) j l a c hac)
    (Affine.ChartTransport.affineHilbertChartFamilyTransport_cocycle R i j k D P hP hD (.of C) a b hab l c hbc hac)

private theorem stableHilbertFamilyTransport_noetherian_self
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j j a a rfl = Iso.refl _ := by
  apply Affine.IsoCocycleDetection.AffineIsoCocycleDetection.overIso_eq_of_noetherianAffinePullbacks
  intro C _ v
  rcases C with ⟨C, instC⟩
  let t : Over.mk (v ≫ T.hom) ⟶ T := Over.homMk v rfl
  rw [Functor.mapIso_refl]
  apply Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoSelf_of_conjugate (FamilyBaseChange.stableHilbertFamilyBaseChangeIso R i D P j a t)
  exact (FamilyBaseChange.stableHilbertFamilyTransport_baseChange R i D P hP hD j j a a rfl t rfl).symm.trans
    (stableHilbertFamilyTransport_affine_self R i D P hP hD C j (t ≫ a))

private theorem stableHilbertFamilyTransport_noetherian_cocycle
    (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hac : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b hab ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l b c hbc =
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l a c hac := by
  apply Affine.IsoCocycleDetection.AffineIsoCocycleDetection.overIso_eq_of_noetherianAffinePullbacks
  intro C _ v
  rcases C with ⟨C, instC⟩
  let t : Over.mk (v ≫ T.hom) ⟶ T := Over.homMk v rfl
  have hab' : (t ≫ a) ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
      (t ≫ b) ≫ ChartPullbacks.stableHilbertChartToRank R i k D P := by
    simpa only [Category.assoc] using congrArg (fun q => t ≫ q) hab
  have hbc' : (t ≫ b) ≫ ChartPullbacks.stableHilbertChartToRank R i k D P =
      (t ≫ c) ≫ ChartPullbacks.stableHilbertChartToRank R i l D P := by
    simpa only [Category.assoc] using congrArg (fun q => t ≫ q) hbc
  have hac' : (t ≫ a) ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
      (t ≫ c) ≫ ChartPullbacks.stableHilbertChartToRank R i l D P := by
    simpa only [Category.assoc] using congrArg (fun q => t ≫ q) hac
  rw [Functor.mapIso_trans]
  apply Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoCocycle_of_conjugate (FamilyBaseChange.stableHilbertFamilyBaseChangeIso R i D P j a t)
    (FamilyBaseChange.stableHilbertFamilyBaseChangeIso R i D P k b t) (FamilyBaseChange.stableHilbertFamilyBaseChangeIso R i D P l c t)
  exact Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoCocycle_of_comparisons
    (FamilyBaseChange.stableHilbertFamilyTransport_baseChange R i D P hP hD j k a b hab t hab').symm
    (FamilyBaseChange.stableHilbertFamilyTransport_baseChange R i D P hP hD k l b c hbc t hbc').symm
    (FamilyBaseChange.stableHilbertFamilyTransport_baseChange R i D P hP hD j l a c hac t hac').symm
    (stableHilbertFamilyTransport_affine_cocycle R i D P hP hD C j k l
      (t ≫ a) (t ≫ b) (t ≫ c) hab' hbc' hac')

theorem stableHilbertFamilyTransport_self
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))} (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j j a a rfl = Iso.refl _ := by
  let U := Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P
  have hs := stableHilbertFamilyTransport_noetherian_self R i D P hP hD j (𝟙 U)
  have hb := FamilyBaseChange.stableHilbertFamilyTransport_baseChange R i D P hP hD j j (𝟙 U) (𝟙 U) rfl a rfl
  rw [hs] at hb
  apply MorphismFactorizationInduction.morphismPredicate_of_comp_id
    (fun b : T ⟶ U => FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j j b b rfl = Iso.refl _) a
  simpa only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl,
    Iso.self_symm_id] using hb

theorem stableHilbertTripleChart_lift
    (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))}
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P) :
    ∃ t : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i ((j.intersection k).intersection l) D P,
      t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i (j.intersection k) l D P hP hD ≫
        IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) = a ∧
      t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i (j.intersection k) l D P hP hD ≫
        IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) = b ∧
      t ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i (j.intersection k) l D P hP hD = c := by
  let Hjk := ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D P hP hD
  obtain ⟨p, hpA, hpB⟩ := Affine.IsoCocycleDetection.AffineIsoCocycleDetection.pullbackLift_exists Hjk a b hab
  have hp : p ≫ ChartPullbacks.stableHilbertChartToRank R i (j.intersection k) D P =
      c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P := by
    rw [← ChartPullbacks.stableHilbertIntersectionLeftMap_toRank R i j k D P hP hD,
      ← Category.assoc, hpA]
    exact hab.trans hbc
  let H := ChartPullbacks.stableHilbertChartIntersection_isPullback R i (j.intersection k) l D P hP hD
  obtain ⟨t, htp, htc⟩ := Affine.IsoCocycleDetection.AffineIsoCocycleDetection.pullbackLift_exists H p c hp
  refine ⟨t, ?_, ?_, htc⟩
  · rw [← Category.assoc, htp]
    exact hpA
  · rw [← Category.assoc, htp]
    exact hpB

private theorem stableHilbertFamilyTransport_pulled_cocycle
    (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {W T : Over (Spec (.of R))}
    (a : W ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : W ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : W ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hac : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hcocycle : FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b hab ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l b c hbc =
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l a c hac)
    (t : T ⟶ W)
    (hab' : (t ≫ a) ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
      (t ≫ b) ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc' : (t ≫ b) ≫ ChartPullbacks.stableHilbertChartToRank R i k D P =
      (t ≫ c) ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hac' : (t ≫ a) ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
      (t ≫ c) ≫ ChartPullbacks.stableHilbertChartToRank R i l D P) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k (t ≫ a) (t ≫ b) hab' ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l (t ≫ b) (t ≫ c) hbc' =
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l (t ≫ a) (t ≫ c) hac' :=
  Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoCocycle_of_comparisons
    (FamilyBaseChange.stableHilbertFamilyTransport_baseChange R i D P hP hD j k a b hab t hab')
    (FamilyBaseChange.stableHilbertFamilyTransport_baseChange R i D P hP hD k l b c hbc t hbc')
    (FamilyBaseChange.stableHilbertFamilyTransport_baseChange R i D P hP hD j l a c hac t hac')
    (Affine.IsoCocycleDetection.AffineIsoCocycleDetection.isoConjugatedFunctorCocycle (Over.pullback t.left)
      (FamilyBaseChange.stableHilbertFamilyBaseChangeIso R i D P j a t)
      (FamilyBaseChange.stableHilbertFamilyBaseChangeIso R i D P k b t)
      (FamilyBaseChange.stableHilbertFamilyBaseChangeIso R i D P l c t) _ _ _ hcocycle)

private theorem stableHilbertFamilyTransport_cocycle_of_factorization
    (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {W T : Over (Spec (.of R))}
    (a₀ : W ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b₀ : W ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c₀ : W ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hab₀ : a₀ ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b₀ ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc₀ : b₀ ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c₀ ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hac₀ : a₀ ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = c₀ ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (h₀ : FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a₀ b₀ hab₀ ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l b₀ c₀ hbc₀ =
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l a₀ c₀ hac₀)
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hfactor : ∃ t : T ⟶ W, t ≫ a₀ = a ∧ t ≫ b₀ = b ∧ t ≫ c₀ = c)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hac : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b hab ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l b c hbc =
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l a c hac :=
  MorphismFactorizationInduction.tripleMorphismFactorization_induction a₀ b₀ c₀
    (fun a b c => ∀
      (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
      (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
      (hac : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P),
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b hab ≪≫
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l b c hbc =
          FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l a c hac)
    (fun t hab hbc hac => stableHilbertFamilyTransport_pulled_cocycle R i D P hP hD j k l
      a₀ b₀ c₀ hab₀ hbc₀ hac₀ h₀ t hab hbc hac) a b c hfactor hab hbc hac

private def tripleChartFirst (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i ((j.intersection k).intersection l) D P ⟶
      Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P :=
  IntersectionMaps.stableHilbertIntersectionLeftMap R i (j.intersection k) l D P hP hD ≫
    IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD

private def tripleChartSecond (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i ((j.intersection k).intersection l) D P ⟶
      Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P :=
  IntersectionMaps.stableHilbertIntersectionLeftMap R i (j.intersection k) l D P hP hD ≫
    IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD

private def tripleChartThird (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i ((j.intersection k).intersection l) D P ⟶
      Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P :=
  IntersectionMaps.stableHilbertIntersectionRightMap R i (j.intersection k) l D P hP hD

private theorem tripleChartFirst_eq (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    tripleChartFirst R i D P hP hD j k l =
      IntersectionMaps.stableHilbertIntersectionLeftMap R i (j.intersection k) l D P hP hD ≫
        IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD := rfl

private theorem tripleChartSecond_eq (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    tripleChartSecond R i D P hP hD j k l =
      IntersectionMaps.stableHilbertIntersectionLeftMap R i (j.intersection k) l D P hP hD ≫
        IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD := rfl

private theorem tripleChartThird_eq (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    tripleChartThird R i D P hP hD j k l =
      IntersectionMaps.stableHilbertIntersectionRightMap R i (j.intersection k) l D P hP hD := rfl

private theorem tripleChartFirstSecond (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    tripleChartFirst R i D P hP hD j k l ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
      tripleChartSecond R i D P hP hD j k l ≫ ChartPullbacks.stableHilbertChartToRank R i k D P := by
  dsimp only [tripleChartFirst, tripleChartSecond]
  simp only [Category.assoc, ChartPullbacks.stableHilbertIntersectionLeftMap_toRank,
    ChartPullbacks.stableHilbertIntersectionRightMap_toRank]

private theorem tripleChartSecondThird (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    tripleChartSecond R i D P hP hD j k l ≫ ChartPullbacks.stableHilbertChartToRank R i k D P =
      tripleChartThird R i D P hP hD j k l ≫ ChartPullbacks.stableHilbertChartToRank R i l D P := by
  dsimp only [tripleChartSecond, tripleChartThird]
  simp only [Category.assoc, ChartPullbacks.stableHilbertIntersectionLeftMap_toRank,
    ChartPullbacks.stableHilbertIntersectionRightMap_toRank]

private theorem tripleChartTransport_cocycle (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k
        (tripleChartFirst R i D P hP hD j k l) (tripleChartSecond R i D P hP hD j k l)
        (tripleChartFirstSecond R i D P hP hD j k l) ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l
        (tripleChartSecond R i D P hP hD j k l) (tripleChartThird R i D P hP hD j k l)
        (tripleChartSecondThird R i D P hP hD j k l) =
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l
        (tripleChartFirst R i D P hP hD j k l) (tripleChartThird R i D P hP hD j k l)
        ((tripleChartFirstSecond R i D P hP hD j k l).trans
          (tripleChartSecondThird R i D P hP hD j k l)) :=
  stableHilbertFamilyTransport_noetherian_cocycle R i D P hP hD j k l
    (tripleChartFirst R i D P hP hD j k l) (tripleChartSecond R i D P hP hD j k l)
    (tripleChartThird R i D P hP hD j k l)
    (tripleChartFirstSecond R i D P hP hD j k l)
    (tripleChartSecondThird R i D P hP hD j k l)
    ((tripleChartFirstSecond R i D P hP hD j k l).trans
      (tripleChartSecondThird R i D P hP hD j k l))

private theorem tripleChartLift_exists
    (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))}
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P) :
    ∃ t : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i ((j.intersection k).intersection l) D P,
      t ≫ tripleChartFirst R i D P hP hD j k l = a ∧
      t ≫ tripleChartSecond R i D P hP hD j k l = b ∧
      t ≫ tripleChartThird R i D P hP hD j k l = c :=
  Affine.IsoCocycleDetection.AffineIsoCocycleDetection.tripleFactorization_of_arrow_eq
    (tripleChartFirst_eq R i D P hP hD j k l)
    (tripleChartSecond_eq R i D P hP hD j k l)
    (tripleChartThird_eq R i D P hP hD j k l)
    (stableHilbertTripleChart_lift R i D P hP hD j k l a b c hab hbc)

theorem stableHilbertFamilyTransport_cocycle
    (j k l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))}
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)
    (hbc : b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hac : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P = c ≫ ChartPullbacks.stableHilbertChartToRank R i l D P) :
    FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b hab ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD k l b c hbc =
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j l a c hac := by
  exact stableHilbertFamilyTransport_cocycle_of_factorization R i D P hP hD j k l
    (W := Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i ((j.intersection k).intersection l) D P) (T := T)
    (tripleChartFirst R i D P hP hD j k l) (tripleChartSecond R i D P hP hD j k l)
    (tripleChartThird R i D P hP hD j k l)
    (tripleChartFirstSecond R i D P hP hD j k l)
    (tripleChartSecondThird R i D P hP hD j k l)
    ((tripleChartFirstSecond R i D P hP hD j k l).trans
      (tripleChartSecondThird R i D P hP hD j k l))
    (tripleChartTransport_cocycle R i D P hP hD j k l) a b c
    (tripleChartLift_exists R i D P hP hD j k l a b c hab hbc) hab hbc hac

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyTransportLaws
