import OAI.RepresentationTheory.Theta.Geometric.Reference.ModelTransport
import OAI.RepresentationTheory.Theta.Geometric.Period.Marking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis

/-! # Level Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The ReferenceFamily fixed ordered level gives the original GeometricTheta division points
on the same algebraic model. This retains every lattice label used in
the away-level marking, through the proved coordinate comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}

section

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.canonicalTorusDiffeomorph_division (F : D.ReferenceAnalyticFiber x)
    (v : D.pel.reference.lattice) :
    F.canonicalTorusDiffeomorph D hg (D.periodLevelPoint x v) =
      (F.toNativeReference D).divisionPoint D.pel.level v := by
  change QuotientAddGroup.mk (F.periodComparison D hg
    ((D.pel.level : ℂ)⁻¹ • D.periodReferenceEmbedding x.val v.val)) =
      QuotientAddGroup.mk ((D.pel.level : ℝ)⁻¹ •
        F.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v.val))
  apply congrArg (QuotientAddGroup.mk : Data.ActiveHeckeThetaData.referenceTangent (s := s) →
    (F.toNativeReference D).periodData.periodTorus)
  refine (map_smul (F.periodComparison D hg) _ _).trans
    ((congrArg ((D.pel.level : ℂ)⁻¹ • ·) (F.periodComparison_projection D hg
      (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v.val))).trans ?_)
  rw [← IsScalarTower.algebraMap_smul ℂ ((D.pel.level : ℝ)⁻¹)]
  simp only [map_inv₀, map_natCast]

end

variable (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)

theorem Data.ActiveHeckeThetaData.PeriodModel.toNativeReferenceModel_division (v : D.pel.reference.lattice) :
    (M.toNativeReferenceModel F).period ((F.toNativeReference D).divisionPoint D.pel.level v) =
      M.period (D.periodLevelPoint x v) :=
  (congrArg (M.toNativeReferenceModel F).period (F.canonicalTorusDiffeomorph_division v).symm).trans
    (M.toNativeReferenceModel_period F (D.periodLevelPoint x v))

def Data.ActiveHeckeThetaData.PeriodModel.fixedReferenceLevel : M.abelianScheme.FullLevel D.pel.level := by
  have h := hg.fullLevel
  let : NeZero D.pel.level := ⟨by omega⟩
  exact (M.toNativeReferenceModel F).fixedFullLevel D.pel.level

theorem Data.ActiveHeckeThetaData.PeriodModel.fixedReferenceLevel_period (v : D.pel.reference.lattice) :
    (((M.fixedReferenceLevel F).hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd
        (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v)))).val =
      M.period (D.periodLevelPoint x v) := by
  have h := hg.fullLevel
  let : NeZero D.pel.level := ⟨by omega⟩
  exact ((M.toNativeReferenceModel F).fixedFullLevel_reference D.pel.level v).trans
    (M.toNativeReferenceModel_division F v)

theorem Data.ActiveHeckeThetaData.PeriodModel.fixedReferenceLevel_independent (G : D.ReferenceAnalyticFiber x) :
    M.fixedReferenceLevel F = M.fixedReferenceLevel G := by
  apply Iso.ext
  apply LevelLabels.fullLevelMap_ext_on_complex M.abelianScheme (M.fixedReferenceLevel F)
  intro a
  apply Subtype.ext
  obtain ⟨v, hv⟩ := D.pel.reference.fixedLevelLabel_surjective hg.reference_admissible D.pel.level a.toAdd
  have ha : Multiplicative.ofAdd
      (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v) = a :=
    congrArg Multiplicative.ofAdd hv
  rw [← ha]
  exact (M.fixedReferenceLevel_period F v).trans (M.fixedReferenceLevel_period G v).symm

end

end OAI.RepresentationTheory.Theta.Geometric
