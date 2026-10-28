import OAI.RepresentationTheory.Theta.Geometric.Reference.PELFiniteMatrix
import OAI.RepresentationTheory.Theta.Geometric.EmbeddingSpan

/-! # PEL Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The rational matrix recovered from an actual PEL isomorphism sends
the original complex period kernel into the target period kernel. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x y : D.domain}
    (R : D.ReferencePELPointData hg x) (S : D.ReferencePELPointData hg y)
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso R.family S.family)

def Data.ActiveHeckeThetaData.ReferencePELPointData.tangentMap : Data.ActiveHeckeThetaData.referenceTangent (s := s) →ₗ[ℂ] Data.ActiveHeckeThetaData.referenceTangent (s := s) :=
  letI : IsMonHom (e.abelian.hom : R.model.abelian.toOver ⟶ S.model.abelian.toOver) := e.abelianGroup
  (S.model.toNativeReferenceModel S.analytic).periodDifferential.symm.toLinearMap.comp
    ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift e.abelian.hom).comp
      (R.model.toNativeReferenceModel R.analytic).periodDifferential.toLinearMap)

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.tangentMap_embedding (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    R.tangentMap S e (R.analytic.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v)) =
      S.analytic.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings
        (D.rationalLinear (R.rationalMatrix S e) v)) := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  let : IsMonHom (e.abelian.hom : R.model.abelian.toOver ⟶ S.model.abelian.toOver) := e.abelianGroup
  have h := congrArg (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods S.model.abelian => t.val)
    (Reference.PELEquiv.referencePELPeriodEquiv_marking (C := R.polarization) (C' := S.polarization) e v)
  change (S.model.toNativeReferenceModel S.analytic).periodDifferential
      (S.analytic.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings
        (Reference.PELEquiv.referencePELFieldEquiv (C := R.polarization) (C' := S.polarization) e v))) =
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift e.abelian.hom ((R.model.toNativeReferenceModel R.analytic).periodDifferential
      (R.analytic.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v))) at h
  apply (S.model.toNativeReferenceModel S.analytic).periodDifferential.injective
  change (S.model.toNativeReferenceModel S.analytic).periodDifferential
      ((S.model.toNativeReferenceModel S.analytic).periodDifferential.symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change _ = (S.model.toNativeReferenceModel S.analytic).periodDifferential
    (S.analytic.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings
      (Matrix.SpecialLinearGroup.toLin'
        (PrincipalUnitaryDeterminant.referencePELRationalSU (C := R.polarization) (C' := S.polarization) e hg.fullLevel).val v)))
  rw [PrincipalUnitaryDeterminant.referencePELRationalSU_linear]
  exact h.symm

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.tangentMap_projection :
    (R.tangentMap S e).comp R.analytic.projection =
      S.analytic.projection.comp (D.rationalAmbient (R.rationalMatrix S e)).toLinearMap := by
  apply EmbeddingSpan.embeddingCoordinates_linear_ext D.pel.reference.embeddings hg.reference_admissible.1
  intro v
  change R.tangentMap S e (R.analytic.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v)) =
    S.analytic.projection (D.rationalAmbient (R.rationalMatrix S e)
      (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v))
  rw [D.rationalAmbient_embedding]
  exact R.tangentMap_embedding S e v

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.rationalMatrix_kernel (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s))
    (hu : u ∈ D.pel.reference.periodFamily x.val) :
    D.rationalAmbient (R.rationalMatrix S e) u ∈ D.pel.reference.periodFamily y.val := by
  rw [← R.analytic.kernel, LinearMap.mem_ker] at hu
  rw [← S.analytic.kernel, LinearMap.mem_ker]
  have h := LinearMap.congr_fun (R.tangentMap_projection S e) u
  change R.tangentMap S e (R.analytic.projection u) =
    S.analytic.projection (D.rationalAmbient (R.rationalMatrix S e) u) at h
  rw [hu, map_zero] at h
  exact h.symm

end

end OAI.RepresentationTheory.Theta.Geometric
