import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceFamilyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointNaturality

/-! # Level Reference Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelReferenceTransport

noncomputable section

/-! The global original Hilbert-family comparison, lifted to the
original full-level universal family. Naturality and the affine
projective equation are proved before any group structure is used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

namespace ParameterConjugation

theorem inverse_square {C : Type*} [Category* C]
    {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B')
    (f : A' ⟶ A) (g : B' ⟶ B) (h : f ≫ e.hom = e'.hom ≫ g) :
    g ≫ e.inv = e'.inv ≫ f := by
  apply (cancel_epi e'.hom).mp
  calc
    _ = (f ≫ e.hom) ≫ e.inv :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ e.inv) h.symm)
    _ = f := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    _ = _ := (e'.hom_inv_id_assoc f).symm

theorem recovered_embeddings {C : Type*} [Category* C]
    {A B X Y P : C} (r : A ≅ X) (s : B ≅ Y) (e : X ≅ Y)
    (a : A ⟶ P) (b : B ⟶ P) (x : X ⟶ P) (y : Y ⟶ P) (c : P ⟶ P)
    (hr : r.hom ≫ x = a) (hs : s.hom ≫ y = b) (he : e.hom ≫ y = x ≫ c) :
    (r ≪≫ e ≪≫ s.symm).hom ≫ b = a ≫ c := by
  have hi : s.inv ≫ b = y := by rw [← hs, s.inv_hom_id_assoc]
  calc
    _ = r.hom ≫ (e.hom ≫ y) := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hi]
    _ = r.hom ≫ (x ≫ c) := congrArg (fun a => r.hom ≫ a) he
    _ = a ≫ c := (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ c) hr)

theorem recovered_embeddings_left {S W : Scheme.{u}}
    {A B X Y : Over S} (r : A ≅ X) (s : B ≅ Y) (e : X ≅ Y)
    (a : A.left ⟶ W) (b : B.left ⟶ W) (x : X.left ⟶ W) (y : Y.left ⟶ W)
    (c : W ⟶ W)
    (hr : r.hom.left ≫ x = a) (hs : s.hom.left ≫ y = b)
    (he : e.hom.left ≫ y = x ≫ c) :
    (r ≪≫ e ≪≫ s.symm).hom.left ≫ b = a ≫ c :=
  recovered_embeddings ((Over.forget S).mapIso r) ((Over.forget S).mapIso s)
    ((Over.forget S).mapIso e) a b x y c hr hs he

end ParameterConjugation

namespace StableHilbertFullLevelOriginalTransport
variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))}
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (.of R)) n H g Hm Hi N)
    (hy : y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
      a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)
    (z : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (.of R)) n H g Hm Hi N)
    (hz : z ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
      b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH)

local notation "S₀" => Spec (CommRingCat.of R)
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S₀ n H g Hm Hi N
local notation "P₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S₀ n H g Hm Hi N
local notation "rY" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso S₀ n H g Hm Hi N y
  (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) hy
local notation "rZ" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso S₀ n H g Hm Hi N z
  (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH) hz

def iso : ((A₀).pullback y.left).scheme ≅ ((A₀).pullback z.left).scheme :=
  rY ≪≫ ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab ≪≫ (rZ).symm

/-- The exact underlying family comparison is natural even when the
local chart and full-level maps use different parenthesizations. -/
theorem natural {U : Over S₀} (u : U ⟶ T)
    (a' : U ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b' : U ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab' : a' ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b' ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (y' : U ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S₀ n H g Hm Hi N)
    (hy' : y' ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N =
      a' ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)
    (z' : U ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S₀ n H g Hm Hi N)
    (hz' : z' ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N =
      b' ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH)
    (ha : u ≫ a = a') (hb : u ≫ b = b') (hY : u ≫ y = y') (hZ : u ≫ z = z') :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
      (Over.homMk u.left (congrArg Over.Hom.left hY) : Over.mk y'.left ⟶ Over.mk y.left)
      (A₀).scheme ≫ (iso R i D H hH hD g Hm Hi N j k a b hab y hy z hz).hom.left =
    (iso R i D H hH hD g Hm Hi N j k a' b' hab' y' hy' z' hz').hom.left ≫
      Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u.left (congrArg Over.Hom.left hZ) : Over.mk z'.left ⟶ Over.mk z.left)
        (A₀).scheme := by
  subst a'
  subst b'
  subst y'
  subst z'
  let rY' := HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso S₀ n H g Hm Hi N (u ≫ y)
    ((u ≫ a) ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) hy'
  let rZ' := HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso S₀ n H g Hm Hi N (u ≫ z)
    ((u ≫ b) ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH) hz'
  have hyN := HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso_natural S₀ n H g Hm Hi N y
    (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) hy (u ≫ y)
    ((u ≫ a) ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) hy' u rfl
    (Category.assoc u a (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)).symm
  have hzN := HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso_natural S₀ n H g Hm Hi N z
    (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH) hz (u ≫ z)
    ((u ≫ b) ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH) hz' u rfl
    (Category.assoc u b (ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH)).symm
  exact ReferenceFamilyNaturality.ParameterConjugation.natural
    ((Over.forget T.left).mapIso (rY)).symm ((Over.forget T.left).mapIso (rZ)).symm
    ((Over.forget U.left).mapIso rY').symm ((Over.forget U.left).mapIso rZ').symm
    ((Over.forget T.left).mapIso (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab))
    ((Over.forget U.left).mapIso (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k
      (u ≫ a) (u ≫ b) hab'))
    _ _ _ _
    (ParameterConjugation.inverse_square ((Over.forget T.left).mapIso (rY))
      ((Over.forget U.left).mapIso rY') _ _ hyN)
    (ParameterConjugation.inverse_square ((Over.forget T.left).mapIso (rZ))
      ((Over.forget U.left).mapIso rZ') _ _ hzN)
    (ReferenceFamilyNaturality.stableHilbertOriginalFamilyTransport_natural R i D H hH hD j k a b hab u hab')

/-- The same underlying isomorphism is the affine coordinate-compatible
one, as detected by the existing projective embeddings. -/
theorem affine_embedding_left
    {C : Type u} [CommRing C] [IsNoetherianRing C] {f : Spec (.of C) ⟶ S₀}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (y : Over.mk f ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S₀ n H g Hm Hi N)
    (hy : y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N =
      a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)
    (z : Over.mk f ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S₀ n H g Hm Hi N)
    (hz : z ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N =
      b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH)
    (v : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (ha : a = v ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (hb : b = v ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) :
    (iso R i D H hH hD g Hm Hi N j k a b hab y hy z hz).hom.left ≫
      ((P₀).baseChange z.left).embedding.left = ((P₀).baseChange y.left).embedding.left ≫
        (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k v).hom.left := by
  exact ParameterConjugation.recovered_embeddings_left
    (HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso S₀ n H g Hm Hi N y
      (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) hy)
    (HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso S₀ n H g Hm Hi N z
      (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH) hz)
    (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab) _ _ _ _ _
    (HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso_embedding_left S₀ n H g Hm Hi N y
      (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) hy)
    (HilbertLevel.PointNaturality.HilbertLevelPullback.pointHilbertIso_embedding_left S₀ n H g Hm Hi N z
      (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH) hz)
    (ReferenceFamilyNaturality.stableHilbertOriginalFamilyTransport_affine_embedding_left R i D H hH hD j k a b hab v ha hb)

theorem affine_embedding
    {C : Type u} [CommRing C] [IsNoetherianRing C] {f : Spec (.of C) ⟶ S₀}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (y : Over.mk f ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S₀ n H g Hm Hi N)
    (hy : y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N =
      a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)
    (z : Over.mk f ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S₀ n H g Hm Hi N)
    (hz : z ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N =
      b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH)
    (v : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (ha : a = v ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (hb : b = v ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) :
    (iso R i D H hH hD g Hm Hi N j k a b hab y hy z hz).hom ≫
      ((P₀).baseChange z.left).embedding = ((P₀).baseChange y.left).embedding ≫
        (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k v).hom := by
  apply Over.OverMorphism.ext
  exact affine_embedding_left R i D H hH hD g Hm Hi N j k a b hab y hy z hz v ha hb

end StableHilbertFullLevelOriginalTransport

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelReferenceTransport
