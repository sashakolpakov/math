import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful

/-! # Level Transition Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitionRecovery

noncomputable section

/-! The glued marked-parameter transition has the actual native
full-level recovery on every Noetherian affine test. The recovered
isomorphism preserves the original group and level and carries the
original projective embedding by the prescribed coordinate change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem precompose_square
    {C : Type*} [Category* C] {T P X Y Z : C}
    (a : T ⟶ P) (l : P ⟶ X) (r : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : l ≫ f = r ≫ g) : (a ≫ l) ≫ f = (a ≫ r) ≫ g :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => a ≫ k) h).trans (Category.assoc _ _ _).symm)

private theorem precompose_square_of_base
    {C : Type*} [Category* C] {T P Q X Y Z : C}
    (a : T ⟶ P) (t : P ⟶ Q) (l : Q ⟶ X) (r : Q ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (b : P ⟶ Y)
    (h : l ≫ f = r ≫ g) (ht : t ≫ r = b) : ((a ≫ t) ≫ l) ≫ f = (a ≫ b) ≫ g :=
  (precompose_square (a ≫ t) l r f g h).trans
    (congrArg (fun k => k ≫ g)
      ((Category.assoc a t r).trans (congrArg (fun k => a ≫ k) ht)))

private theorem pullback_precompose_square
    {C : Type*} [Category* C] {T X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (a : T ⟶ pullback f g) :
    (a ≫ pullback.fst f g) ≫ f = (a ≫ pullback.snd f g) ≫ g :=
  precompose_square a (pullback.fst f g) (pullback.snd f g) f g
    (pullback.condition (f := f) (g := g))

private theorem pullback_precompose_square_of_base
    {C : Type*} [Category* C] {T P X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (a : T ⟶ P) (t : P ⟶ pullback f g) (b : P ⟶ Y)
    (ht : t ≫ pullback.snd f g = b) :
    ((a ≫ t) ≫ pullback.fst f g) ≫ f = (a ≫ b) ≫ g :=
  precompose_square_of_base a t (pullback.fst f g) (pullback.snd f g) f g b
    (pullback.condition (f := f) (g := g)) ht

private structure OverlapPointData
    {C : Type*} [Category* C] {T X Y A B I : C}
    (f : X ⟶ A) (g : Y ⟶ B) (l : I ⟶ A) (r : I ⟶ B) where
  base : T ⟶ I
  source : T ⟶ X
  target : T ⟶ Y
  source_eq : source ≫ f = base ≫ l
  target_eq : target ≫ g = base ≫ r

private def pullbackOverlapPointData
    {C : Type*} [Category* C] {T X Y A B I : C}
    (f : X ⟶ A) (g : Y ⟶ B) (l : I ⟶ A) (r : I ⟶ B)
    [HasPullback f l] [HasPullback g r]
    (t : pullback f l ⟶ pullback g r)
    (ht : t ≫ pullback.snd g r = pullback.snd f l)
    (c : T ⟶ pullback f l) : OverlapPointData (T := T) f g l r where
  base := c ≫ pullback.snd f l
  source := c ≫ pullback.fst f l
  target := (c ≫ t) ≫ pullback.fst g r
  source_eq := pullback_precompose_square f l c
  target_eq := pullback_precompose_square_of_base g r c t (pullback.snd f l) ht

private theorem pullbackOverlapPointData_property
    {C : Type*} [Category* C] {T X Y A B I : C}
    (f : X ⟶ A) (g : Y ⟶ B) (l : I ⟶ A) (r : I ⟶ B)
    [HasPullback f l] [HasPullback g r]
    (t : pullback f l ⟶ pullback g r)
    (ht : t ≫ pullback.snd g r = pullback.snd f l)
    (c : T ⟶ pullback f l)
    (P : (T ⟶ I) → (T ⟶ X) → (T ⟶ Y) → Prop)
    (h : let q := pullbackOverlapPointData f g l r t ht c
      P q.base q.source q.target) :
    P (c ≫ pullback.snd f l) (c ≫ pullback.fst f l) ((c ≫ t) ≫ pullback.fst g r) := h

namespace StableHilbertFullLevelAffineRecovery
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] [IsNoetherianRing C] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {f : Spec (.of C) ⟶ Spec (.of R)}
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)
    (hu : u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels =
      b ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)

local notation "S₀" => Spec (CommRingCat.of R)
local notation "y" => u ≫ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels

omit [IsNoetherianRing C] in
include hu in
theorem sourceEquation :
    y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N =
      AffineProjectiveEmbedding.StableHilbertAffineTransport.leftPoint R i D H hH hD j k b :=
  (LevelForgetful.StableHilbertFullLevel.point_forget R i j D H hH g Hm Hi N labels u).trans
    (congrArg (fun a => a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) hu)

local notation "he" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitionRecovery.StableHilbertFullLevelAffineRecovery.sourceEquation R i D H hH hD g Hm Hi N labels j k b u hu
local notation "yR" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineLevelTransport.StableHilbertAffineFullLevelTransport.point R i D H hH hD j k b g Hm Hi N y he

variable (v : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)
    (hv : v ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels =
      b ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)

local notation "yv" => v ≫ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels

include hu hv in
theorem targetPoint : yv = yR := by
  let : IsLocallyNoetherian (Over.mk f).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of C)))
  have hV : yv ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S₀ n H g Hm Hi N =
      AffineProjectiveEmbedding.StableHilbertAffineTransport.rightPoint R i D H hH hD j k b :=
    (LevelForgetful.StableHilbertFullLevel.point_forget R i k D H hH g Hm Hi N labels v).trans
      (congrArg (fun a => a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH) hv)
  have hR := AffineLevelTransport.StableHilbertAffineFullLevelTransport.point_forget R i D H hH hD j k b g Hm Hi N y he
  apply HilbertLevel.MarkedUniqueness.HilbertLevelPullback.points_eq_of_hilbert_eq_markedPoints (T := Over.mk f)
    S₀ n H g Hm Hi N yv yR (hV.trans hR.symm)
  intro label
  obtain ⟨z, rfl⟩ := labels.surjective label
  have hL := (LevelForgetful.StableHilbertFullLevel.point_markedPoint R i j D H hH g Hm Hi N labels u z).trans
    (congrArg (fun a => PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H a z) hu)
  have hK := (LevelForgetful.StableHilbertFullLevel.point_markedPoint R i k D H hH g Hm Hi N labels v z).trans
    (congrArg (fun a => PrescribedPointCriterion.stableHilbertPrescribedPoint R i k D H a z) hv)
  have hC := AffineLevelTransport.StableHilbertAffineFullLevelTransport.point_markedPoint R i D H hH hD j k b g Hm Hi N y he (labels z)
  have hT := AffineMarkedTransport.stableHilbertPrescribedPoint_overlap R i j D H hH hD k b z
  exact hK.trans (hT.symm.trans
    ((congrArg (fun a => a ≫ (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k b).hom) hL).symm.trans hC.symm))

include hD hu hv in
theorem nativeFullLevelRecovery :
    ∃ e : ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S₀ n H g Hm Hi N).pullback (y).left).scheme ≅
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S₀ n H g Hm Hi N).pullback (yv).left).scheme,
      ∃ hgroup : IsMonHom e.hom,
        let _ : IsMonHom e.hom := hgroup
        ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S₀ n H g Hm Hi N).pullback (y).left).transport e =
            (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S₀ n H g Hm Hi N).pullback (yv).left ∧
          e.hom ≫ ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S₀ n H g Hm Hi N).baseChange
            (yv).left).embedding =
          ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S₀ n H g Hm Hi N).baseChange
            (y).left).embedding ≫ (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k b).hom := by
  rw [targetPoint R i D H hH hD g Hm Hi N labels j k b u hu v hv]
  refine ⟨AffineLevelTransport.StableHilbertAffineFullLevelTransport.groupIso R i D H hH hD j k b g Hm Hi N y he,
    inferInstance, ?_, ?_⟩
  · exact AffineLevelTransport.StableHilbertAffineFullLevelTransport.groupIso_level R i D H hH hD j k b g Hm Hi N y he
  · exact AffineLevelTransport.StableHilbertAffineFullLevelTransport.groupIso_embedding R i D H hH hD j k b g Hm Hi N y he

end StableHilbertFullLevelAffineRecovery
namespace StableHilbertFullLevelTransition
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] [IsNoetherianRing C] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {f : Spec (.of C) ⟶ Spec (.of R)}
    (c : Over.mk f ⟶ pullback
      (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)
      (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))

local notation "ij" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels
local notation "ik" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels
local notation "lj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD
local notation "lk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD
local notation "uL" => c ≫ pullback.fst ij lj
local notation "uR" => (c ≫ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitions.StableHilbertFullLevelTransition.forward R i D H hH hD g Hm Hi N labels j k) ≫ pullback.fst ik lk
local notation "b₀" => c ≫ pullback.snd ij lj
local notation "yL" => uL ≫ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels
local notation "yR₀" => uR ≫ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N
local notation "l₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N
local notation "P₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N

private theorem overlapPointData_nativeRecovery
    (q : OverlapPointData (T := Over.mk f) ij ik lj lk) :
    let y := q.source ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels
    let z := q.target ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels
    ∃ e : ((A₀).pullback y.left).scheme ≅ ((A₀).pullback z.left).scheme,
      ∃ hgroup : IsMonHom e.hom,
        let _ : IsMonHom e.hom := hgroup
        ((l₀).pullback y.left).transport e = (l₀).pullback z.left ∧
          e.hom ≫ ((P₀).baseChange z.left).embedding =
          ((P₀).baseChange y.left).embedding ≫
            (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k q.base).hom :=
  StableHilbertFullLevelAffineRecovery.nativeFullLevelRecovery (C := C) (f := f)
    R i D H hH hD g Hm Hi N labels j k q.base q.source q.source_eq q.target q.target_eq

theorem forward_affine_nativeRecovery :
    ∃ e : ((A₀).pullback (yL).left).scheme ≅ ((A₀).pullback (yR₀).left).scheme,
      ∃ hgroup : IsMonHom e.hom,
        let _ : IsMonHom e.hom := hgroup
        Abelian.Schemes.AbelianScheme.FullLevel.transport (g := g) (N := N)
            (A := (A₀).pullback (yL).left) (B := (A₀).pullback (yR₀).left)
            (Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := A₀) l₀ (yL).left) e =
          Abelian.Schemes.AbelianScheme.FullLevel.pullback (g := g) (N := N) (A := A₀) l₀ (yR₀).left ∧
          e.hom ≫ ((P₀).baseChange (yR₀).left).embedding =
          ((P₀).baseChange (yL).left).embedding ≫
            (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k b₀).hom := by
  have h := overlapPointData_nativeRecovery (C := C) (f := f)
    R i D H hH hD g Hm Hi N labels j k
    (pullbackOverlapPointData ij ik lj lk
      (LevelTransitions.StableHilbertFullLevelTransition.forward R i D H hH hD g Hm Hi N labels j k)
      (LevelTransitions.StableHilbertFullLevelTransition.forward_base R i D H hH hD g Hm Hi N labels j k) c)
  exact pullbackOverlapPointData_property ij ik lj lk
    (LevelTransitions.StableHilbertFullLevelTransition.forward R i D H hH hD g Hm Hi N labels j k)
    (LevelTransitions.StableHilbertFullLevelTransition.forward_base R i D H hH hD g Hm Hi N labels j k) c
    (fun b u v =>
      let y := u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels
      let z := v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels
      ∃ e : ((A₀).pullback y.left).scheme ≅ ((A₀).pullback z.left).scheme,
        ∃ hgroup : IsMonHom e.hom,
          let _ : IsMonHom e.hom := hgroup
          ((l₀).pullback y.left).transport e = (l₀).pullback z.left ∧
            e.hom ≫ ((P₀).baseChange z.left).embedding =
            ((P₀).baseChange y.left).embedding ≫
              (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k b).hom) h

end StableHilbertFullLevelTransition

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelTransitionRecovery
