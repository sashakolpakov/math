import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorCoordinates
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Adelic Tensor Density -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorDensity.TestTransport

noncomputable section

/-! Density of the prescribed rational embeddings in the tensor and
quadratic models of the finite adeles. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable (F : Type) [Field F] [NumberField F]

theorem denseRange_finiteCoefficientEmbedding : DenseRange (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding F) := by
  have h := (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorHomeomorph F).surjective.denseRange.comp
    (RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F) (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorHomeomorph F).continuous
  simpa only [Function.comp_def, AdelicTensorCoordinates.TestTransport.scalarAdelicTensorHomeomorph_rational] using h

theorem scalarAdelicTensorRingEquiv_symm_rational (x : F) :
    (AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv F).symm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding F x) =
      algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) x := by
  rw [← AdelicTensorCoordinates.TestTransport.scalarAdelicTensorRingEquiv_rational, RingEquiv.symm_apply_apply]

theorem denseRange_quadraticDiagonal (a : F) :
    DenseRange (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) a) := by
  let e := RepresentationTheory.Theta.Adelic.SpecialUnitary.quadraticHomeomorph (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a)
  have h := e.symm.surjective.denseRange.comp
    ((RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F).prodMap (RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F))
    e.symm.continuous
  have hr : Set.range (fun p : F × F => e.symm
      (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) p.1, algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) p.2)) =
      Set.range (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) a) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(⟨p.1, p.2⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a), rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨(z.re, z.im), rfl⟩
  intro z
  have hz := h z
  change z ∈ closure (Set.range (fun p : F × F => e.symm
    (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) p.1, algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) p.2))) at hz
  rwa [hr] at hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorDensity.TestTransport
