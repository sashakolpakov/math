import OAI.AlgebraicGeometry.Projective.PresentationMono
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelReferenceTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.ParameterIsoLocality

/-! # Level Reference Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelReferenceRecovery

noncomputable section

/-! The global original-family comparison preserves the original group
and ordered full level on a stable overlap. Its affine restrictions are
identified with the actual bounded classifier recovery by their original
projective embeddings, then the group and level equations descend. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem precomp_square {C : Type*} [Category* C]
    {W X Y Z V : C} (u : W ⟶ X) (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ V) (d : V ⟶ Z) (h : a ≫ b = c ≫ d) :
    (u ≫ a) ≫ b = (u ≫ c) ≫ d :=
  (Category.assoc _ _ _).trans ((congrArg (fun q => u ≫ q) h).trans (Category.assoc _ _ _).symm)

private theorem iso_eq_of_native_embedding
    {S W : Scheme.{u}} {X Y : Over S} (e q : X ≅ Y)
    (j : Y.left ⟶ W) [hjMono : Mono j]
    (h : e.hom.left ≫ j = q.hom.left ≫ j) : e = q := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  exact (cancel_mono j).mp h

private theorem composition_eq_left
    {S : Scheme.{u}} {X Y Z : Over S}
    (q : X ⟶ Y) (j : Y ⟶ Z) (i : X ⟶ Z) (h : q ≫ j = i) :
    q.left ≫ j.left = i.left := congrArg Over.Hom.left h

private theorem dependentProperty_of_unique {α : Sort*}
    (e : α) (Q : α → Prop) (P : ∀ q, Q q → Prop) (B : α → Prop)
    (unique : ∀ q, B q → e = q)
    (h : ∃ q, ∃ hq : Q q, P q hq ∧ B q) : ∃ he : Q e, P e he := by
  obtain ⟨q, hq, hp, hb⟩ := h
  cases unique q hb
  exact ⟨hq, hp⟩

namespace StableHilbertFullLevelOriginalRecovery
variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

variable {T : Over (Spec (CommRingCat.of R))}
    (t : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD))

include hu hv in
theorem rankEquation :
    (u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H := by
  rw [hu, hv, Category.assoc, Category.assoc,
    ChartPullbacks.stableHilbertIntersectionLeftMap_toRank, ChartPullbacks.stableHilbertIntersectionRightMap_toRank]

/-- The isomorphism is the global original raw-Hilbert-family transport,
conjugated by the original full-level universal-family recoveries. -/
def iso : (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).pullback (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left).scheme ≅ (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).pullback (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left).scheme :=
  LevelReferenceTransport.StableHilbertFullLevelOriginalTransport.iso R i D H hH hD g Hm Hi N j k
    (u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) (v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) (rankEquation R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)) (LevelForgetful.StableHilbertFullLevel.point_forget R i j D H hH g Hm Hi N labels u)
    (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)) (LevelForgetful.StableHilbertFullLevel.point_forget R i k D H hH g Hm Hi N labels v)

theorem natural {U : Over (Spec (CommRingCat.of R))} (c : U ⟶ T)
    (hu' : (c ≫ u) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = (c ≫ t) ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (hv' : (c ≫ v) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = (c ≫ t) ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)) :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
      (Over.homMk c.left (congrArg Over.Hom.left (Category.assoc c u (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).symm) :
        Over.mk ((c ≫ u) ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left ⟶ Over.mk (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left) ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).scheme ≫
        (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom.left =
    (iso R i D H hH hD g Hm Hi N labels j k (c ≫ t) (c ≫ u) hu' (c ≫ v) hv').hom.left ≫
      Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk c.left (congrArg Over.Hom.left (Category.assoc c v (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).symm) :
          Over.mk ((c ≫ v) ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left ⟶ Over.mk (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left) ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).scheme :=
  LevelReferenceTransport.StableHilbertFullLevelOriginalTransport.natural R i D H hH hD g Hm Hi N j k
    (u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) (v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) (rankEquation R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)) (LevelForgetful.StableHilbertFullLevel.point_forget R i j D H hH g Hm Hi N labels u)
    (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)) (LevelForgetful.StableHilbertFullLevel.point_forget R i k D H hH g Hm Hi N labels v)
    c ((c ≫ u) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) ((c ≫ v) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels))
    (rankEquation R i D H hH hD g Hm Hi N labels j k (c ≫ t) (c ≫ u) hu' (c ≫ v) hv')
    ((c ≫ u) ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)) (LevelForgetful.StableHilbertFullLevel.point_forget R i j D H hH g Hm Hi N labels (c ≫ u))
    ((c ≫ v) ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)) (LevelForgetful.StableHilbertFullLevel.point_forget R i k D H hH g Hm Hi N labels (c ≫ v))
    (Category.assoc c u (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)).symm (Category.assoc c v (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)).symm
    (Category.assoc c u (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).symm (Category.assoc c v (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).symm

theorem affine_embedding_left
    {C : Type u} [CommRing C] [IsNoetherianRing C] {f : Spec (.of C) ⟶ (Spec (CommRingCat.of R))}
    (t : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)) :
    (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom.left ≫
      (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChange (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left).embedding.left =
    (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChange (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left).embedding.left ≫
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k t).hom.left :=
  LevelReferenceTransport.StableHilbertFullLevelOriginalTransport.affine_embedding_left R i D H hH hD g Hm Hi N j k
    (u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)) (v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels)) (rankEquation R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)) (LevelForgetful.StableHilbertFullLevel.point_forget R i j D H hH g Hm Hi N labels u)
    (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)) (LevelForgetful.StableHilbertFullLevel.point_forget R i k D H hH g Hm Hi N labels v) t hu hv

theorem affine_embedding
    {C : Type u} [CommRing C] [IsNoetherianRing C] {f : Spec (.of C) ⟶ (Spec (CommRingCat.of R))}
    (t : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)) :
    (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom ≫
      (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChange (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left).embedding =
    (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChange (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left).embedding ≫
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k t).hom := by
  apply Over.OverMorphism.ext
  exact affine_embedding_left R i D H hH hD g Hm Hi N labels j k t u hu v hv

private theorem affine_iso_eq_left
    {C : Type u} [CommRing C] [IsNoetherianRing C] {f : Spec (.of C) ⟶ (Spec (CommRingCat.of R))}
    (t : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD))
    (q : ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N).pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left).scheme ≅ ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N).pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).scheme)
    (hq : q.hom.left ≫ ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).embedding.left = ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left).embedding.left ≫ (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k t).hom.left) :
    iso R i D H hH hD g Hm Hi N labels j k t u hu v hv = q := by
  have hm : Mono (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).embedding).left := Projective.PresentationMono.HilbertConstruction.projectivePresentationEmbeddingMono
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange
      (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left)
  exact iso_eq_of_native_embedding (hjMono := hm) (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv) q (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).embedding).left
    ((affine_embedding_left R i D H hH hD g Hm Hi N labels j k t u hu v hv).trans hq.symm)

private theorem affine_iso_eq
    {C : Type u} [CommRing C] [IsNoetherianRing C] {f : Spec (.of C) ⟶ (Spec (CommRingCat.of R))}
    (t : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD))
    (q : ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N).pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left).scheme ≅ ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N).pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).scheme)
    (hq : q.hom ≫ ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).embedding = ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left).embedding ≫ (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k t).hom) :
    iso R i D H hH hD g Hm Hi N labels j k t u hu v hv = q := by
  exact affine_iso_eq_left R i D H hH hD g Hm Hi N labels j k t u hu v hv q
    (composition_eq_left q.hom ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).embedding (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left).embedding ≫ (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k t).hom) hq)

private theorem affine_isFullLevel
    {C : Type u} [CommRing C] [IsNoetherianRing C] {f : Spec (.of C) ⟶ (Spec (CommRingCat.of R))}
    (t : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)) :
    ∃ hg : IsMonHom (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom,
      letI := hg
      Abelian.Schemes.AbelianScheme.FullLevel.transport (g := g) (N := N)
        (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N).pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left) (B := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N).pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left)
        (Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N) (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left)
        (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv) =
      Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N) (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left := by
  have h := LevelTransitionRecovery.StableHilbertFullLevelAffineRecovery.nativeFullLevelRecovery
    (C := C) (f := f) R i D H hH hD g Hm Hi N labels j k t u hu v hv
  exact dependentProperty_of_unique (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (fun q => IsMonHom q.hom)
    (fun q hq => let _ : IsMonHom q.hom := hq
      Abelian.Schemes.AbelianScheme.FullLevel.transport (g := g) (N := N)
        (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N).pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left) (B := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N).pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left)
        (Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (.of R)) n H g Hm Hi N) (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left) q =
      Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (.of R)) n H g Hm Hi N) (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left)
    (fun q => q.hom ≫ ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).embedding = ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left).embedding ≫ (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k t).hom)
    (affine_iso_eq R i D H hH hD g Hm Hi N labels j k t u hu v hv) h

private theorem affine_isFullLevel_ring
    (C : CommRingCat.{u}) [IsNoetherianRing C] {f : Spec C ⟶ (Spec (CommRingCat.of R))}
    (t : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : Over.mk f ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)) :
    ∃ hg : IsMonHom (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom,
      letI := hg
      Abelian.Schemes.AbelianScheme.FullLevel.transport (g := g) (N := N)
        (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N).pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left) (B := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N).pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left)
        (Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N) (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left)
        (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv) =
      Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N) (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left := by
  rcases C with ⟨C, instC⟩
  exact affine_isFullLevel (C := C) (f := f)
    R i D H hH hD g Hm Hi N labels j k t u hu v hv

/-- A locally Noetherian base suffices to prove the full group and level
claims. No reducedness hypothesis is used. -/
theorem isFullLevel [IsLocallyNoetherian T.left] :
    ∃ hg : IsMonHom (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom,
      letI := hg
      Abelian.Schemes.AbelianScheme.FullLevel.transport (g := g) (N := N)
        (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N).pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left) (B := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N).pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left)
        (Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N) (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left)
        (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv) =
      Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N) (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left := by
  let C := T.left.affineOpenCover.openCover
  let ys : ∀ a, C.X a ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (CommRingCat.of R)) n H g Hm Hi N).left :=
    fun a => ((HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T a ≫ u) ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left
  let zs : ∀ a, C.X a ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (CommRingCat.of R)) n H g Hm Hi N).left :=
    fun a => ((HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T a ≫ v) ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left
  have hy : ∀ a, C.f a ≫ (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left = ys a := fun a =>
    congrArg Over.Hom.left (Category.assoc (HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T a) u (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).symm
  have hz : ∀ a, C.f a ≫ (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left = zs a := fun a =>
    congrArg Over.Hom.left (Category.assoc (HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T a) v (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).symm
  apply ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N )).fullLevelParameterIso_of_openCover (g := g) (N := N) ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N)) (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left
    (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv) C ys zs hy hz
  intro a
  have : IsOpenImmersion (T.left.affineOpenCover.f a) :=
    inferInstanceAs (IsOpenImmersion (C.f a))
  let : IsNoetherianRing (T.left.affineOpenCover.X a) :=
    isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (T.left.affineOpenCover.f a))
  let c := HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T a
  have hu' : (c ≫ u) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = (c ≫ t) ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) := precomp_square c u (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) t (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) hu
  have hv' : (c ≫ v) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = (c ≫ t) ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) := precomp_square c v (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) t (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) hv
  obtain ⟨hg, hl⟩ := affine_isFullLevel_ring
    R i D H hH hD g Hm Hi N labels j k (T.left.affineOpenCover.X a) (c ≫ t) (c ≫ u) hu' (c ≫ v) hv'
  exact ⟨iso R i D H hH hD g Hm Hi N labels j k
      (c ≫ t) (c ≫ u) hu' (c ≫ v) hv', hg, hl,
    natural R i D H hH hD g Hm Hi N labels j k t u hu v hv c hu' hv'⟩

instance iso_isMonHom [IsLocallyNoetherian T.left] :
    IsMonHom (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom :=
  (isFullLevel R i D H hH hD g Hm Hi N labels j k t u hu v hv).choose

theorem iso_level [IsLocallyNoetherian T.left] :
    Abelian.Schemes.AbelianScheme.FullLevel.transport (g := g) (N := N)
        (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N).pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left) (B := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N).pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left)
        (Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N) (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left)
        (iso R i D H hH hD g Hm Hi N labels j k t u hu v hv) =
      Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)) (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N) (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left :=
  (isFullLevel R i D H hH hD g Hm Hi N labels j k t u hu v hv).choose_spec

end StableHilbertFullLevelOriginalRecovery

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelReferenceRecovery
