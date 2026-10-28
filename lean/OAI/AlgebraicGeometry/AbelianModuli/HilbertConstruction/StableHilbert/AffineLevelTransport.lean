import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointGraphBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.MarkedUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelRecovery

/-! # Affine Level Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineLevelTransport

noncomputable section

/-! Transport an actual original full-level Hilbert point across an
actual affine stable-chart overlap. The constructed point recovers the
same original group and full level, and every marked section changes by
the actual overlap coordinate isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem map_eqToIso_comp_indexed
    {C D : Type*} [Category* C] [Category* D] {α : Sort*}
    (X : α → C) (F : C ⥤ D) {x y : α} (h : x = y)
    {Z : D} (i : ∀ a, F.obj (X a) ⟶ Z) :
    F.map (eqToIso (congrArg X h)).hom ≫ i y = i x := by
  cases h
  change F.map (𝟙 (X x)) ≫ i x = i x
  rw [F.map_id, Category.id_comp]

private theorem equalBasePullback_embedding_left {S T : Scheme.{u}} {X : Over S}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) {f g : T ⟶ S} (h : f = g) :
    (eqToIso (congrArg (fun a => (Over.pullback a).obj X) h)).hom.left ≫
      (P.baseChange g).embedding.left = (P.baseChange f).embedding.left := by
  exact map_eqToIso_comp_indexed (fun a => (Over.pullback a).obj X) (Over.forget T) h
    (Z := (Projective.ProjectivePresentations.projectiveSpaceOver T P.dimension).left) (fun a => (P.baseChange a).embedding.left)

private theorem isoTrans_triangle_left
    {S W : Scheme.{u}} {X Y Z : Over S}
    (e : X ≅ Y) (q : Y ≅ Z) (i : Z.left ⟶ W) (j : Y.left ⟶ W) (k : X.left ⟶ W)
    (hq : q.hom.left ≫ i = j) (he : e.hom.left ≫ j = k) :
    (e ≪≫ q).hom.left ≫ i = k := by
  change (e.hom.left ≫ q.hom.left) ≫ i = k
  exact (Category.assoc _ _ _).trans ((congrArg (fun z => e.hom.left ≫ z) hq).trans he)

private theorem isoTrans_coordinate_left
    {S W : Scheme.{u}} {X Y Z : Over S}
    (e : X ≅ Y) (q : Y ≅ Z) (i : Z.left ⟶ W) (j : Y.left ⟶ W) (k : X.left ⟶ W)
    (a : W ⟶ W) (hq : q.hom.left ≫ i = j ≫ a) (he : e.hom.left ≫ j = k) :
    (e ≪≫ q).hom.left ≫ i = k ≫ a :=
  isoTrans_triangle_left e q i (j ≫ a) (k ≫ a) hq
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ a) he))

private def rawCoordinateTwistingIso
    {S : Scheme.{u}} {X Y : Over S} {n : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (e : X ≅ Y)
    (z : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤)))
    (h : e.hom.left ≫ j.left = i.left ≫ (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z).hom.left) :
    (Scheme.Modules.pullback e.hom.left).obj
      ((Scheme.Modules.pullback j.left).obj (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf) ≅
      (Scheme.Modules.pullback i.left).obj (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf := by
  have he : e.hom ≫ j = i ≫ (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z).hom := by
    apply Over.OverMorphism.ext
    exact h
  exact PresentedGroupCoordinateTransport.projectiveEmbeddingCoordinateTwistingIso i j e z he

private theorem fullLevelSection_transport_eq
    {S : Scheme.{u}} {g N : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (l : A.FullLevel N) (k : B.FullLevel N) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (h : l.transport e = k) (label : Multiplicative (Fin (2 * g) → ZMod N)) :
    B.fullLevelGlobalSection k label = A.fullLevelGlobalSection l label ≫ e.hom.left :=
  (congrArg (fun v : B.FullLevel N => B.fullLevelGlobalSection v label) h).symm.trans
    (Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_transport l e label)

private theorem marked_coordinate
    {C : Type*} [Category* C] {T X Y Z : C}
    (s : T ⟶ X) (t : T ⟶ Y) (e : X ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z) (a : Z ⟶ Z)
    (ht : t = s ≫ e) (he : e ≫ j = i ≫ a) : t ≫ j = (s ≫ i) ≫ a :=
  (congrArg (fun f => f ≫ j) ht).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => s ≫ f) he).trans (Category.assoc _ _ _).symm))

private structure FullLevelRecoveryData
    (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (T : Over S) (A : Abelian.Schemes.AbelianScheme g T.left) (level : A.FullLevel N)
    (b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H)
    (k : A.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left) where
  point : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n H g Hm Hi N
  iso : A.scheme ≅
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback point.left).scheme
  group : IsMonHom iso.hom
  level_eq :
    let _ : IsMonHom iso.hom := group
    level.transport iso = (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n H g Hm Hi N).pullback point.left
  forget_eq : point ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S n H g Hm Hi N = b
  embedding_eq : iso.hom.left ≫
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange point.left).embedding.left = k

private def nativeFullLevelRecoveryData
    (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ) (g : ℕ)
    {T : Over S} (A : Abelian.Schemes.AbelianScheme g T.left)
    (b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H)
    (e : A.scheme ≅ (Over.pullback b.left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.scheme)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (eL : (((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).ampleLineBundle.pullback
      e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf)
    (Hm Hi : Polynomial ℚ)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ProjectiveGraphBounds P Hm Hi)
    (N : ℕ) [NeZero N] (level : A.FullLevel N)
    (k : A.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left)
    (he : e.hom.left ≫ ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left = k) :
    FullLevelRecoveryData S n H g Hm Hi N T A level b k where
  point := Intrinsic.AbelianLift.NativeHilbertAbelianLift.fullLevelClassifier S n H g A b e P eL Hm Hi hb N level
  iso := Intrinsic.LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelRecovery S n H g A b e P eL Hm Hi hb N level
  group := Intrinsic.LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelRecovery_isMonHom S n H g A b e P eL Hm Hi hb N level
  level_eq := Intrinsic.LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelRecovery_level S n H g A b e P eL Hm Hi hb N level
  forget_eq := Intrinsic.AbelianLift.NativeHilbertAbelianLift.fullLevelClassifier_forget S n H g A b e P eL Hm Hi hb N level
  embedding_eq :=
    (Intrinsic.LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelRecovery_embedding_left S n H g A b e P eL Hm Hi hb N level).trans he

namespace StableHilbertAffineFullLevelTransport

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {n m : ℕ} (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {f : Spec (.of C) ⟶ Spec (.of R)}
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (y : Over.mk f ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (.of R)) n H g Hm Hi N)
    (hy : y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
      AffineProjectiveEmbedding.StableHilbertAffineTransport.leftPoint R i D H hH hD j k b)

local notation "S₀" => Spec (CommRingCat.of R)
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S₀ n H g Hm Hi N) y.left
local notation "P₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.baseChange (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S₀ n H g Hm Hi N) y.left
local notation "l₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.pullback (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S₀ n H g Hm Hi N) y.left
local notation "Q" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Presentation.NativeHilbertAbelianLift.presentation S₀ n H
local notation "bL" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveEmbedding.StableHilbertAffineTransport.leftPoint R i D H hH hD j k b
local notation "bR" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveEmbedding.StableHilbertAffineTransport.rightPoint R i D H hH hD j k b
local notation "a" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k b

private def leftRecovery : (A₀).scheme ≅ (Over.pullback (bL).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S₀ n H).family.scheme :=
  HilbertLevel.ProjectiveRecovery.HilbertLevelPullback.universalFamilyPullbackIso S₀ n H g Hm Hi N y.left ≪≫
    eqToIso (congrArg (fun z => (Over.pullback z).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S₀ n H).family.scheme)
      (congrArg Over.Hom.left hy))

omit [IsNoetherianRing C] in
private theorem leftRecovery_embedding_left :
    (leftRecovery R i D H hH hD j k b g Hm Hi N y hy).hom.left ≫
      ((Q).baseChange (bL).left).embedding.left = (P₀).embedding.left := by
  let e := HilbertLevel.ProjectiveRecovery.HilbertLevelPullback.universalFamilyPullbackIso S₀ n H g Hm Hi N y.left
  let q := eqToIso (congrArg (fun z => (Over.pullback z).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S₀ n H).family.scheme)
    (congrArg Over.Hom.left hy))
  have hq : q.hom.left ≫ ((Q).baseChange (bL).left).embedding.left =
      ((Q).baseChange (y.left ≫ (HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N).left)).embedding.left :=
    equalBasePullback_embedding_left Q (congrArg Over.Hom.left hy)
  exact isoTrans_triangle_left e q _ _ _ hq
    (HilbertLevel.ProjectiveRecovery.HilbertLevelPullback.universalFamilyPullbackIso_embedding_left S₀ n H g Hm Hi N y.left)

def hilbertRecovery : (A₀).scheme ≅ (Over.pullback (bR).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S₀ n H).family.scheme :=
  leftRecovery R i D H hH hD j k b g Hm Hi N y hy ≪≫
    AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso R i D H hH hD j k b

theorem hilbertRecovery_embedding_left :
    (hilbertRecovery R i D H hH hD j k b g Hm Hi N y hy).hom.left ≫ ((Q).baseChange (bR).left).embedding.left =
      (P₀).embedding.left ≫ (a).hom.left := by
  let e := leftRecovery R i D H hH hD j k b g Hm Hi N y hy
  let q := AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso R i D H hH hD j k b
  exact isoTrans_coordinate_left e q _ _ _ (a).hom.left
    (AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso_embedding_left R i D H hH hD j k b)
    (leftRecovery_embedding_left R i D H hH hD j k b g Hm Hi N y hy)

theorem hilbertRecovery_embedding :
    (hilbertRecovery R i D H hH hD j k b g Hm Hi N y hy).hom ≫ ((Q).baseChange (bR).left).embedding =
      (P₀).embedding ≫ (a).hom := by
  apply Over.OverMorphism.ext
  exact hilbertRecovery_embedding_left R i D H hH hD j k b g Hm Hi N y hy

def hilbertRecoveryTwistingIso :
    (((Q).baseChange (bR).left).ampleLineBundle.pullback
      (hilbertRecovery R i D H hH hD j k b g Hm Hi N y hy).hom.left).sheaf ≅ (P₀).ampleLineBundle.sheaf := by
  let x := b ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D H
  let h := StableChartFrames.stablePolynomialIntersection_frameRelated R i j k x
  let i₀ : (A₀).scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n := (P₀).embedding
  let j₀ : (Over.pullback (bR).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S₀ n H).family.scheme ⟶
      Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n := ((Q).baseChange (bR).left).embedding
  let : IsClosedImmersion i₀.left := (P₀).closedImmersion
  let : IsClosedImmersion j₀.left := ((Q).baseChange (bR).left).closedImmersion
  exact rawCoordinateTwistingIso i₀ j₀
    (hilbertRecovery R i D H hH hD j k b g Hm Hi N y hy)
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform
      (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv (Scheme.ΓSpecIso (.of C)).inv.hom h.choose)).symm
    (hilbertRecovery_embedding_left R i D H hH hD j k b g Hm Hi N y hy)

local notation "eR" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineLevelTransport.StableHilbertAffineFullLevelTransport.hilbertRecovery R i D H hH hD j k b g Hm Hi N y hy
local notation "eL" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineLevelTransport.StableHilbertAffineFullLevelTransport.hilbertRecoveryTwistingIso R i D H hH hD j k b g Hm Hi N y hy
local notation "hb" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointGraphBounds.fixedDimensionHilbertFullLevelPoint_graphBounds S₀ n H g Hm Hi N y

private def recoveryData :
    FullLevelRecoveryData S₀ n H g Hm Hi N (Over.mk f) A₀ l₀ bR ((P₀).embedding.left ≫ (a).hom.left) :=
  nativeFullLevelRecoveryData (T := Over.mk f) S₀ n H g A₀ bR eR P₀ eL Hm Hi hb N l₀
    ((P₀).embedding.left ≫ (a).hom.left)
    (hilbertRecovery_embedding_left R i D H hH hD j k b g Hm Hi N y hy)

def point : Over.mk f ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S₀ n H g Hm Hi N :=
  (recoveryData R i D H hH hD j k b g Hm Hi N y hy).point

theorem point_forget :
    StableHilbertAffineFullLevelTransport.point R i D H hH hD j k b g Hm Hi N y hy ≫
      HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N = bR :=
  (recoveryData R i D H hH hD j k b g Hm Hi N y hy).forget_eq

local notation "yR" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineLevelTransport.StableHilbertAffineFullLevelTransport.point R i D H hH hD j k b g Hm Hi N y hy

def groupIso : (A₀).scheme ≅
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S₀ n H g Hm Hi N).pullback (yR).left).scheme :=
  (recoveryData R i D H hH hD j k b g Hm Hi N y hy).iso

instance groupIso_isMonHom : IsMonHom (groupIso R i D H hH hD j k b g Hm Hi N y hy).hom :=
  (recoveryData R i D H hH hD j k b g Hm Hi N y hy).group

theorem groupIso_level :
    (l₀).transport (groupIso R i D H hH hD j k b g Hm Hi N y hy) =
      (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S₀ n H g Hm Hi N).pullback (yR).left :=
  (recoveryData R i D H hH hD j k b g Hm Hi N y hy).level_eq

theorem groupIso_embedding_left :
    (groupIso R i D H hH hD j k b g Hm Hi N y hy).hom.left ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S₀ n H g Hm Hi N).baseChange (yR).left).embedding.left =
        (P₀).embedding.left ≫ (a).hom.left :=
  (recoveryData R i D H hH hD j k b g Hm Hi N y hy).embedding_eq

theorem groupIso_embedding :
    (groupIso R i D H hH hD j k b g Hm Hi N y hy).hom ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S₀ n H g Hm Hi N).baseChange (yR).left).embedding =
        (P₀).embedding ≫ (a).hom := by
  apply Over.OverMorphism.ext
  exact groupIso_embedding_left R i D H hH hD j k b g Hm Hi N y hy

theorem point_markedPoint (label : Multiplicative (Fin (2 * g) → ZMod N)) :
    HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint S₀ n H g Hm Hi N yR label =
      HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint S₀ n H g Hm Hi N y label ≫ (a).hom := by
  let e := groupIso R i D H hH hD j k b g Hm Hi N y hy
  let A₁ := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S₀ n H g Hm Hi N).pullback (yR).left
  let l₁ : A₁.FullLevel N := (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S₀ n H g Hm Hi N).pullback (yR).left
  let P₁ : Projective.ProjectivePresentations.ProjectivePresentation A₁.scheme :=
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S₀ n H g Hm Hi N).baseChange (yR).left
  have ht : A₁.fullLevelGlobalSection l₁ label = (A₀).fullLevelGlobalSection l₀ label ≫ e.hom.left :=
    fullLevelSection_transport_eq l₀ l₁ e
      (groupIso_level R i D H hH hD j k b g Hm Hi N y hy) label
  apply Over.OverMorphism.ext
  exact marked_coordinate ((A₀).fullLevelGlobalSection l₀ label)
    (A₁.fullLevelGlobalSection l₁ label) e.hom.left (P₀).embedding.left P₁.embedding.left
    (a).hom.left ht (groupIso_embedding_left R i D H hH hD j k b g Hm Hi N y hy)

end StableHilbertAffineFullLevelTransport

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineLevelTransport
