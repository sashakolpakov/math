import OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleLine
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldHomogeneityBaseChange
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldHomogeneityFamilyMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Countable Ample Homogeneous Pair -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleHomogeneousPair.Geometric

noncomputable section

/-! An ample line and a homogeneous line on the same original abelian
scheme descend to one countable algebraically closed field, retaining
both classes, the group, ampleness, and universal homogeneity. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem exists_countable_ample_homogeneous_pair (hL : L.IsAmple)
    (hN : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N)) :
    ∃ D : CountableAmpleLine.Geometric.CountableAmpleLineModel A L,
      ∃ J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle D.abelian.scheme.left,
        AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass D.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) ∧
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
          (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap (Spec.map (CommRingCat.ofHom D.field.subtype))
            A.scheme D.abelian.scheme D.recovery) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N := by
  obtain ⟨D₀⟩ := CountableAmpleLine.Geometric.exists_countable_ample_line_model A L hL
  obtain ⟨G, hG, hGa, hFG, J, hJ⟩ :=
    AbelianScheme.IsogenyQuotient.Countable.RecoveredLines.Construction.countable_recovered_line_model_exists D₀.field D₀.abelian A D₀.recovery N
  let : Countable G := hG
  let : IsAlgClosed G := hGa
  let v : Spec (.of G) ⟶ Spec (.of D₀.field) := (AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction.subfieldParameter D₀.field G hFG).hom
  let u := Spec.map (CommRingCat.ofHom G.subtype)
  let w := Spec.map (CommRingCat.ofHom D₀.field.subtype)
  let B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of G)) := D₀.abelian.pullback v
  let : IsMonHom D₀.recovery.hom := D₀.recovery_group
  let e : A.scheme ≅ (B.pullback u).scheme := AbelianScheme.IsogenyQuotient.StagedRecovery.Construction.stagedAbelianRecovery D₀.abelian A v u w
    (AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction.subfieldParameterRestriction D₀.field G hFG).w D₀.recovery
  let : IsMonHom e.hom := AbelianScheme.IsogenyQuotient.StagedRecovery.Construction.stagedAbelianRecovery_isMonHom D₀.abelian A v u w
    (AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction.subfieldParameterRestriction D₀.field G hFG).w D₀.recovery
  let c := AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u A.scheme B.scheme e
  let p₀ : B.scheme.left ⟶ D₀.abelian.scheme.left := pullback.fst D₀.abelian.scheme.hom v
  let M := D₀.line.pullback p₀
  let : IsAffineHom v := inferInstanceAs (IsAffineHom
    (Spec.map (CommRingCat.ofHom (Subfield.inclusion hFG))))
  let : IsAffineHom p₀ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback D₀.abelian.scheme.hom v).flip inferInstance
  have hM : M.IsAmple := D₀.ample.pullback_of_isAffineHom p₀
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass p₀ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D₀.line)) = _
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact (congrArg (fun t => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D₀.line))
      (AbelianScheme.IsogenyQuotient.StagedRecovery.Construction.stagedAbelianRecovery_totalMap_comp D₀.abelian A v u w
        (AbelianScheme.IsogenyQuotient.Countable.ParameterLines.Construction.subfieldParameterRestriction D₀.field G hFG).w D₀.recovery)).trans D₀.line_recovery
  let p : (B.pullback u).scheme.left ⟶ B.scheme.left := pullback.fst B.scheme.hom u
  have hclasses : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (J.pullback p)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass p (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J)) = _
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact hJ
  have hJk : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (B.pullback u) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (J.pullback p)) :=
    (FieldHomogeneityFamilyMaps.Geometric.homogeneousLine_iso_iff A (B.pullback u) e _).mp (hclasses.symm ▸ hN)
  have hJhom : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) :=
    FieldHomogeneityBaseChange.Geometric.homogeneousLine_of_baseChange B J u (hM.projectivePresentation B.scheme.hom) hJk
  let D : CountableAmpleLine.Geometric.CountableAmpleLineModel A L := {
    field := G
    abelian := B
    recovery := e
    recovery_group := inferInstance
    line := M
    ample := hM
    line_recovery := hc }
  exact ⟨D, J, hJhom, hJ⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleHomogeneousPair.Geometric
