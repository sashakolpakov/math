import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedFamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceTransportCocycle

/-! # Level Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelComparison.StableHilbertLevelComparison

noncomputable section

/-! Canonical comparisons of actual marked families at chart points with
the same stable rank point. The overlap is constructed by its pullback
property, and the family maps satisfy the original native cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem lift_eq_left {C : Type*} [Category* C]
    {I X Y Z T : C} {l : I ⟶ X} {r : I ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (p : IsPullback l r f g) (x : T ⟶ X) (y : T ⟶ Y) (h : x ≫ f = y ≫ g) :
    x = p.lift x y h ≫ l := (p.lift_fst x y h).symm

private theorem lift_eq_right {C : Type*} [Category* C]
    {I X Y Z T : C} {l : I ⟶ X} {r : I ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (p : IsPullback l r f g) (x : T ⟶ X) (y : T ⟶ Y) (h : x ≫ f = y ≫ g) :
    y = p.lift x y h ≫ r := (p.lift_snd x y h).symm

private theorem cocycle_of_iso_conjugation {C : Type*} [Category* C]
    {A B D X Y Z : C} (a : A ≅ X) (b : B ≅ Y) (c : D ≅ Z)
    {e : A ≅ B} {f : B ≅ D} {g : A ≅ D} (h : e ≪≫ f = g) :
    (a.symm ≪≫ e ≪≫ b) ≪≫ (b.symm ≪≫ f ≪≫ c) = a.symm ≪≫ g ≪≫ c := by
  rw [← h]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

/-- The existing marked family at the actual parameter point. -/
def familyAt (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))} (a : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) : Level.Data.AbelianSchemeWithFullLevel g N T.left :=
  (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).pullback a.left

/-- The prescribed normalized Hilbert line at the actual point. -/
def lineAt (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))} (a : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) :
    Line.Bundles.LineBundle (familyAt R i D H hH g Hm Hi N labels j a).abelian.scheme.left :=
  ((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian.zeroNormalizedBundle
    (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels).ampleLineBundle).pullback
      (CategoryTheory.Limits.pullback.fst
        (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian.scheme.hom a.left)

variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) {T : Over (Spec (.of R))}
    (a : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (b : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels))
    (hab : (a ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (b ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)

def overlap : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H :=
  (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D H hH hD).lift (a ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) (b ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) hab

private theorem overlap_eq_lift : overlap R i D H hH hD g Hm Hi N labels j k a b hab =
    (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D H hH hD).lift
      (a ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)
      (b ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) hab := rfl

theorem leftEquation : a ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = overlap R i D H hH hD g Hm Hi N labels j k a b hab ≫
    IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD := by
  rw [overlap_eq_lift]
  exact lift_eq_left (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D H hH hD)
    (a ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)
    (b ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) hab

theorem rightEquation : b ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = overlap R i D H hH hD g Hm Hi N labels j k a b hab ≫
    IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD := by
  rw [overlap_eq_lift]
  exact lift_eq_right (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D H hH hD)
    (a ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)
    (b ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) hab

def familyIso : (familyAt R i D H hH g Hm Hi N labels j a).abelian.scheme ≅
    (familyAt R i D H hH g Hm Hi N labels k b).abelian.scheme :=
  NormalizedFamilyTransport.StableHilbertFullLevelOriginalRecovery.familyIso R i D H hH hD g Hm Hi N labels j k
    (overlap R i D H hH hD g Hm Hi N labels j k a b hab) a
    (leftEquation R i D H hH hD g Hm Hi N labels j k a b hab) b
    (rightEquation R i D H hH hD g Hm Hi N labels j k a b hab)

instance familyIso_isMonHom [IsLocallyNoetherian T.left] :
    IsMonHom (familyIso R i D H hH hD g Hm Hi N labels j k a b hab).hom :=
  NormalizedFamilyTransport.StableHilbertFullLevelOriginalRecovery.familyIso_isMonHom R i D H hH hD g Hm Hi N labels j k
    (overlap R i D H hH hD g Hm Hi N labels j k a b hab) a
    (leftEquation R i D H hH hD g Hm Hi N labels j k a b hab) b
    (rightEquation R i D H hH hD g Hm Hi N labels j k a b hab)

theorem familyIso_level [IsLocallyNoetherian T.left] :
    (familyAt R i D H hH g Hm Hi N labels j a).level.transport
      (familyIso R i D H hH hD g Hm Hi N labels j k a b hab) =
        (familyAt R i D H hH g Hm Hi N labels k b).level :=
  NormalizedFamilyTransport.StableHilbertFullLevelOriginalRecovery.familyIso_level R i D H hH hD g Hm Hi N labels j k
    (overlap R i D H hH hD g Hm Hi N labels j k a b hab) a
    (leftEquation R i D H hH hD g Hm Hi N labels j k a b hab) b
    (rightEquation R i D H hH hD g Hm Hi N labels j k a b hab)

theorem familyIso_line [IsLocallyNoetherian T.left] :
    Line.Bundles.LineBundle.pullbackClass (familyIso R i D H hH hD g Hm Hi N labels j k a b hab).hom.left
      (Line.Bundles.LineBundle.classOf (lineAt R i D H hH g Hm Hi N labels k b)) =
        Line.Bundles.LineBundle.classOf (lineAt R i D H hH g Hm Hi N labels j a) :=
  NormalizedFamilyTransport.StableHilbertFullLevelOriginalRecovery.familyIso_normalized_class R i D H hH hD g Hm Hi N labels j k
    (overlap R i D H hH hD g Hm Hi N labels j k a b hab) a
    (leftEquation R i D H hH hD g Hm Hi N labels j k a b hab) b
    (rightEquation R i D H hH hD g Hm Hi N labels j k a b hab)

/-- This cocycle is an identity of the actual underlying family maps
on all test schemes, before using Noetherianity or polarization. -/
theorem familyIso_cocycle
    (l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (c : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i l D H hH g Hm Hi N labels))
    (hbc : (b ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H =
      (c ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i l D H)
    (hac : (a ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (c ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i l D H) :
    familyIso R i D H hH hD g Hm Hi N labels j k a b hab ≪≫
      familyIso R i D H hH hD g Hm Hi N labels k l b c hbc =
    familyIso R i D H hH hD g Hm Hi N labels j l a c hac := by
  let ea := LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i j D H hH g Hm Hi N labels a
  let eb := LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels b
  let ec := LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i l D H hH g Hm Hi N labels c
  have h₀ := ReferenceTransportCocycle.StableHilbertFullLevelOriginalTransport.cocycle R i D H hH hD j k l
    (a ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) (b ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) (c ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i l D H hH g Hm Hi N labels)) hab hbc hac g Hm Hi N
    (a ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)) (b ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)) (c ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i l D H hH g Hm Hi N labels))
    (LevelForgetful.StableHilbertFullLevel.point_forget R i j D H hH g Hm Hi N labels a)
    (LevelForgetful.StableHilbertFullLevel.point_forget R i k D H hH g Hm Hi N labels b)
    (LevelForgetful.StableHilbertFullLevel.point_forget R i l D H hH g Hm Hi N labels c)
  have h := cocycle_of_iso_conjugation ea eb ec h₀
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelComparison.StableHilbertLevelComparison
