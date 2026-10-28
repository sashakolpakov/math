import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceNormalizedLine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelFamilyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.IsoConjugation

/-! # Normalized Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedFamilyTransport

noncomputable section

/-! The existing marked-chart families have globally compatible
zero-normalized projective lines on each locally Noetherian overlap.
This supplies the actual graph-enhancement transport between charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem normalized_class_of_embedding
    {S Z T : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme g Z)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (Q : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
    (a : T ⟶ S) (b : T ⟶ Z)
    (e : (A.pullback a).scheme ≅ (B.pullback b).scheme) [hgroup : IsMonHom e.hom]
    (hn : P.dimension = Q.dimension)
    (he : HEq (e.hom.left ≫ (Q.baseChange b).embedding.left) (P.baseChange a).embedding.left) :
    Line.Bundles.LineBundle.pullbackClass e.hom.left
      (Line.Bundles.LineBundle.classOf ((B.zeroNormalizedBundle Q.ampleLineBundle).pullback
        (pullback.fst B.scheme.hom b))) =
    Line.Bundles.LineBundle.classOf ((A.zeroNormalizedBundle P.ampleLineBundle).pullback
      (pullback.fst A.scheme.hom a)) := by
  have hE : Line.Bundles.LineBundle.pullbackClass e.hom.left
      (Line.Bundles.LineBundle.classOf (Q.baseChange b).ampleLineBundle) =
      Line.Bundles.LineBundle.classOf (P.baseChange a).ampleLineBundle :=
    Quotient.sound ⟨Q.baseChangeSectionRecovery (P.baseChange a) (P.baseChange a).ampleLineBundle
      (P.baseChange a).canonicalSectionData b e hn.symm he⟩
  have hQ : Line.Bundles.LineBundle.classOf (Q.baseChange b).ampleLineBundle =
      Line.Bundles.LineBundle.classOf (Q.ampleLineBundle.pullback (pullback.fst B.scheme.hom b)) :=
    Quotient.sound ⟨Q.baseChangeTwistingBundleIso b⟩
  have hP : Line.Bundles.LineBundle.classOf (P.baseChange a).ampleLineBundle =
      Line.Bundles.LineBundle.classOf (P.ampleLineBundle.pullback (pullback.fst A.scheme.hom a)) :=
    Quotient.sound ⟨P.baseChangeTwistingBundleIso a⟩
  exact A.zeroNormalizedParameter_class_transport B P.ampleLineBundle Q.ampleLineBundle a b e
    ((congrArg (Line.Bundles.LineBundle.pullbackClass e.hom.left) hQ.symm).trans (hE.trans hP))

private theorem recovered_normalized_class
    {S : Scheme.{u}} {g N : ℕ} {F : Level.Data.AbelianSchemeWithFullLevel g N S}
    {P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme} {U T : Over S} {c : U ⟶ T}
    {V : Over T.left} {d : Over.mk c.left ⟶ V}
    (E : Embedded.LevelIso.ParameterPullbackTwiceRecovery F P c d) :
    Line.Bundles.LineBundle.pullbackClass E.data.data.iso.hom.left
      (Line.Bundles.LineBundle.classOf
        ((((F.pullback T.hom).pullback V.hom).abelian.zeroNormalizedBundle
          (Embedded.LevelIso.fullLevelProjectiveBaseChange (F.pullback T.hom)
            (Embedded.LevelIso.fullLevelProjectiveBaseChange F P T.hom) V.hom).ampleLineBundle).pullback
          (pullback.fst ((F.pullback T.hom).pullback V.hom).abelian.scheme.hom d.left))) =
    Line.Bundles.LineBundle.classOf ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
      (pullback.fst F.abelian.scheme.hom U.hom)) := by
  exact normalized_class_of_embedding (hgroup := E.data.data.group)
    F.abelian ((F.pullback T.hom).pullback V.hom).abelian P
    (Embedded.LevelIso.fullLevelProjectiveBaseChange (F.pullback T.hom)
      (Embedded.LevelIso.fullLevelProjectiveBaseChange F P T.hom) V.hom)
    U.hom d.left E.data.data.iso rfl (heq_of_eq E.data.data.embedding_eq)

private theorem line_class_conjugation
    {S : Scheme.{u}} {A B C D : Over S}
    (r : A ≅ B) (e : A ≅ C) (s : C ≅ D)
    (LA : Line.Bundles.LineBundle A.left) (LB : Line.Bundles.LineBundle B.left)
    (LC : Line.Bundles.LineBundle C.left) (LD : Line.Bundles.LineBundle D.left)
    (hr : Line.Bundles.LineBundle.pullbackClass r.hom.left (Line.Bundles.LineBundle.classOf LB) = Line.Bundles.LineBundle.classOf LA)
    (he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf LC) = Line.Bundles.LineBundle.classOf LA)
    (hs : Line.Bundles.LineBundle.pullbackClass s.hom.left (Line.Bundles.LineBundle.classOf LD) = Line.Bundles.LineBundle.classOf LC) :
    Line.Bundles.LineBundle.pullbackClass (r.symm ≪≫ e ≪≫ s).hom.left (Line.Bundles.LineBundle.classOf LD) =
      Line.Bundles.LineBundle.classOf LB := by
  change Line.Bundles.LineBundle.pullbackClass (r.inv.left ≫ e.hom.left ≫ s.hom.left) _ = _
  rw [Line.Bundles.LineBundle.pullbackClass_comp, Line.Bundles.LineBundle.pullbackClass_comp, hs, he]
  exact Line.Bundles.LineBundle.inverseRecovery r LA LB hr

namespace StableHilbertFullLevel
variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    {T : Over (Spec (.of R))} (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)

theorem pointFamilyIso_normalized_class :
    Line.Bundles.LineBundle.pullbackClass (LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i j D H hH g Hm Hi N labels u).hom.left
      (Line.Bundles.LineBundle.classOf ((((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).abelian.zeroNormalizedBundle ((LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels)).ampleLineBundle).pullback
        (pullback.fst ((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).abelian.scheme.hom u.left))) =
    Line.Bundles.LineBundle.classOf ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N)).zeroNormalizedBundle ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N)).ampleLineBundle).pullback
      (pullback.fst ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N)).scheme.hom ((u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left)) := by
  exact recovered_normalized_class (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u)
end StableHilbertFullLevel

namespace StableHilbertFullLevelOriginalRecovery
variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

variable {T : Over (Spec (.of R))}
    (t : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD))

/-- The global original comparison on the two actual marked families. -/
def familyIso : (((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).abelian.pullback u.left).scheme ≅ (((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels)).abelian.pullback v.left).scheme :=
  ((LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i j D H hH g Hm Hi N labels u)).symm ≪≫ (LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso R i D H hH hD g Hm Hi N labels j k t u hu v hv) ≪≫ (LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels v)

instance familyIso_isMonHom [IsLocallyNoetherian T.left] :
    IsMonHom (familyIso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom := by
  let A₀ := FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N
  let A₁ := A₀.pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left
  let B₁ := (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian.pullback u.left
  let A₂ := A₀.pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left
  let B₂ := (LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels).abelian.pullback v.left
  let r : A₁.scheme ≅ B₁.scheme := LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i j D H hH g Hm Hi N labels u
  let e : A₁.scheme ≅ A₂.scheme := LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso R i D H hH hD g Hm Hi N labels j k t u hu v hv
  let s : A₂.scheme ≅ B₂.scheme := LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels v
  let : IsMonHom r.hom := LevelFamilyComparison.StableHilbertLevel.pointFamilyIso_isMonHom R i j D H hH g Hm Hi N labels u
  let : IsMonHom e.hom := LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso_isMonHom R i D H hH hD g Hm Hi N labels j k t u hu v hv
  let : IsMonHom s.hom := LevelFamilyComparison.StableHilbertLevel.pointFamilyIso_isMonHom R i k D H hH g Hm Hi N labels v
  exact Level.IsoConjugation.isoConjugation_isMonHom r e s

theorem familyIso_level [IsLocallyNoetherian T.left] :
    (((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).level.pullback u.left).transport
      (familyIso R i D H hH hD g Hm Hi N labels j k t u hu v hv) = ((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels)).level.pullback v.left := by
  let A₀ := FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N
  let A₁ := A₀.pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left
  let B₁ := (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian.pullback u.left
  let A₂ := A₀.pullback (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left
  let B₂ := (LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels).abelian.pullback v.left
  let r : A₁.scheme ≅ B₁.scheme := LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i j D H hH g Hm Hi N labels u
  let e : A₁.scheme ≅ A₂.scheme := LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso R i D H hH hD g Hm Hi N labels j k t u hu v hv
  let s : A₂.scheme ≅ B₂.scheme := LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels v
  let : IsMonHom r.hom := LevelFamilyComparison.StableHilbertLevel.pointFamilyIso_isMonHom R i j D H hH g Hm Hi N labels u
  let : IsMonHom e.hom := LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso_isMonHom R i D H hH hD g Hm Hi N labels j k t u hu v hv
  let : IsMonHom s.hom := LevelFamilyComparison.StableHilbertLevel.pointFamilyIso_isMonHom R i k D H hH g Hm Hi N labels v
  let lA₁ : A₁.FullLevel N := (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (.of R)) n H g Hm Hi N).pullback
    (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left
  let lB₁ : B₁.FullLevel N := (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).level.pullback u.left
  let lA₂ : A₂.FullLevel N := (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel (Spec (.of R)) n H g Hm Hi N).pullback
    (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left
  let lB₂ : B₂.FullLevel N := (LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels).level.pullback v.left
  have hr : lA₁.transport r = lB₁ :=
    LevelFamilyComparison.StableHilbertLevel.pointFamilyIso_level R i j D H hH g Hm Hi N labels u
  have he : lA₁.transport e = lA₂ := LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso_level R i D H hH hD g Hm Hi N labels j k t u hu v hv
  have hs : lA₂.transport s = lB₂ :=
    LevelFamilyComparison.StableHilbertLevel.pointFamilyIso_level R i k D H hH g Hm Hi N labels v
  exact Abelian.Schemes.AbelianScheme.FullLevel.transport_conjugation A₁ B₁ A₂ B₂ r e s lA₁ lB₁ lA₂ lB₂ hr he hs

theorem familyIso_normalized_class [IsLocallyNoetherian T.left] :
    Line.Bundles.LineBundle.pullbackClass (familyIso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom.left
      (Line.Bundles.LineBundle.classOf ((((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels)).abelian.zeroNormalizedBundle ((LevelParameter.StableHilbertLevel.presentation R i k D H hH g Hm Hi N labels)).ampleLineBundle).pullback
        (pullback.fst ((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels)).abelian.scheme.hom v.left))) =
    Line.Bundles.LineBundle.classOf ((((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).abelian.zeroNormalizedBundle ((LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels)).ampleLineBundle).pullback
      (pullback.fst ((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).abelian.scheme.hom u.left)) := by
  let A₀ := FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (.of R)) n H g Hm Hi N
  let P₀ := FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N
  let y := u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels
  let z := v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels
  exact line_class_conjugation
    (LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i j D H hH g Hm Hi N labels u)
    (LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (LevelPointFamilyIso.StableHilbertLevel.pointFamilyIso R i k D H hH g Hm Hi N labels v)
    ((A₀.zeroNormalizedBundle P₀.ampleLineBundle).pullback (pullback.fst A₀.scheme.hom y.left))
    (((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian.zeroNormalizedBundle
      (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels).ampleLineBundle).pullback
      (pullback.fst (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian.scheme.hom u.left))
    ((A₀.zeroNormalizedBundle P₀.ampleLineBundle).pullback (pullback.fst A₀.scheme.hom z.left))
    (((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels).abelian.zeroNormalizedBundle
      (LevelParameter.StableHilbertLevel.presentation R i k D H hH g Hm Hi N labels).ampleLineBundle).pullback
      (pullback.fst (LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels).abelian.scheme.hom v.left))
    (StableHilbertFullLevel.pointFamilyIso_normalized_class R i j D H hH g Hm Hi N labels u)
    (ReferenceNormalizedLine.StableHilbertLevelReferenceRecovery.normalized_class R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (StableHilbertFullLevel.pointFamilyIso_normalized_class R i k D H hH g Hm Hi N labels v)

include hu hv in
theorem enhancement_nonempty_iff [IsLocallyNoetherian T.left] (δ : Fin g → ℕ) (d : ℕ) :
    Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).pullback u.left)
      ((((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).abelian.zeroNormalizedBundle ((LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels)).ampleLineBundle).pullback
        (pullback.fst ((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).abelian.scheme.hom u.left)) d) ↔
    Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels)).pullback v.left)
      ((((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels)).abelian.zeroNormalizedBundle ((LevelParameter.StableHilbertLevel.presentation R i k D H hH g Hm Hi N labels)).ampleLineBundle).pullback
        (pullback.fst ((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels)).abelian.scheme.hom v.left)) d) :=
  @GraphPower.EnhancementRestriction.graphPowerEnhancement_nonempty_iff_of_groupIso T.left g N δ (((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels)).pullback u.left) (((LevelParameter.StableHilbertLevel.family R i k D H hH g Hm Hi N labels)).pullback v.left) _ _ d
    (familyIso R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (familyIso_isMonHom R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (familyIso_normalized_class R i D H hH hD g Hm Hi N labels j k t u hu v hv)

end StableHilbertFullLevelOriginalRecovery

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedFamilyTransport
