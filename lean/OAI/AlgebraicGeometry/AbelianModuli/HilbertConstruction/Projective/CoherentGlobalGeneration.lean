import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistGlobalGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Shift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ProjectionFormula

/-! # Coherent Global Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentGlobalGeneration

noncomputable section

/-! Sufficiently positive twists of every finite-type quasicoherent module on an actual projective quotient have finite global generators. The bound comes from the constructed finite negative-twist quotient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projective_finiteType_eventually_hasFiniteGlobalGenerators
    (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (Tensor.ProductSheaf.tensorModule M (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf) := by
  classical
  let D := @NegativeTwistCover.ProjectiveNegativeTwistCover.ofFiniteType R _ n I M
    ‹M.IsQuasicoherent› ‹M.IsFiniteType›
  let : Finite D.index := D.finite
  let : Fintype D.index := Fintype.ofFinite D.index
  refine ⟨Finset.univ.sup D.degree + 1, fun d hd => ?_⟩
  let L := ProjectiveTwisting.Bundle.projectiveTwistingBundle I d
  let F := (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L).functor
  let Q : D.index → (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules :=
    fun i => (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (D.degree i)).sheaf
  have hQ : ∀ i, HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (F.obj (Q i)) := by
    intro i
    have hi : D.degree i < d :=
      lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i)) (Nat.lt_of_succ_le hd)
    let e : F.obj (Q i) ≅ (ProjectiveTwisting.Bundle.projectiveTwistingBundle I (d - D.degree i)).sheaf :=
      LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso L (Q i) ≪≫
        ProjectiveTwisting.Shift.projectiveTwisting_negative_sub_iso I (D.degree i) d (Nat.le_of_lt hi)
    exact (TwistGlobalGeneration.projectiveTwistingBundle_positive_hasFiniteGlobalGenerators I
      (d - D.degree i) (Nat.sub_pos_of_lt hi)).of_iso e.symm
  have : Epi (Sigma.desc D.component) := D.epi
  have : Epi (Sigma.desc (fun i => F.map (D.component i))) :=
    EpimorphicCoproductFamilies.epi_sigmaDesc_map F Q D.component
  have hgen := HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.coproduct (fun i => F.obj (Q i)) hQ
  exact (hgen.of_epi (Sigma.desc (fun i => F.map (D.component i)))).of_iso
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso L M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentGlobalGeneration
