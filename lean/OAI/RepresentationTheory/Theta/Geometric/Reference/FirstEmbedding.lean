import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.HodgeKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Quotient

/-! # First Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding

noncomputable section

/-! The distinguished first block of the literal reference period
family is exactly its normalized ball line. -/

open scoped Classical

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Quotient

def firstEmbeddingInclusion {s : ℕ} (d : Fin s) : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
  (LinearMap.single ℂ (fun _ : Fin s => Geometry.ComplexBall.PrescribedSignsB.Vec × Geometry.ComplexBall.PrescribedSignsB.Vec) d).comp
    (LinearMap.inl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec Geometry.ComplexBall.PrescribedSignsB.Vec)

theorem firstEmbeddingInclusion_prescribed {s : ℕ} (d : Fin s) (signs : Fin s → Bool)
    (B : Fin s → Geometry.ComplexBall.PrescribedSignsB.Vec → Geometry.ComplexBall.PrescribedSignsB.Vec → ℂ) (hB : ∀ i v, B i v 0 = 0) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.Prescribed B d signs z (firstEmbeddingInclusion d v) ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} := by
  constructor
  · intro h
    simpa [Geometry.ComplexBall.PrescribedSignsB.Prescribed, firstEmbeddingInclusion, hB] using h d
  · intro hv i
    by_cases hi : i = d
    · subst i
      simpa [firstEmbeddingInclusion, hB] using hv
    · simp [hi, firstEmbeddingInclusion]

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

def referenceFirstComplexInclusion : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :=
  (P.referenceComplexCoordinates hP).symm.toLinearMap.comp (firstEmbeddingInclusion P.distinguished)

theorem referenceFirstComplexInclusion_kernel (z : P.domain) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    P.referenceComplexCoordinates hP (referenceFirstComplexInclusion P hP v) ∈ P.periodFamily z.val ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val} := by
  change P.referenceComplexCoordinates hP ((P.referenceComplexCoordinates hP).symm _) ∈ _ ↔ _
  rw [LinearEquiv.apply_symm_apply, (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 z.val z.property).1]
  exact firstEmbeddingInclusion_prescribed P.distinguished P.compactSigns
    (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]))
    (fun i u => by simp [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal]) z.val v

theorem nativeReferenceFirst_kernel {z : P.domain} {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z}
    (M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    M.nativeComplexReferenceMarking (referenceFirstComplexInclusion P hP v) ∈
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection M.abelian).ker ↔ v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val} :=
  (M.nativeReferenceKernel _).trans (referenceFirstComplexInclusion_kernel P hP z v)

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding
