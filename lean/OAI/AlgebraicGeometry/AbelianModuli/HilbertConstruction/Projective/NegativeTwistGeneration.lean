import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistMorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.EpimorphismCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CoproductSectionSurjection

/-! # Negative Twist Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistGeneration

noncomputable section

/-! Every finite-type quasicoherent module on an actual homogeneous projective quotient is a quotient of a finite direct sum of constructed negative twists. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projective_quasicoherent_finiteType_negativeTwist_quotient
    (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (ι : Type u) (_ : Finite ι) (d : ι → ℕ)
      (φ : ∀ i, (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (d i)).sheaf ⟶ M), Epi (Sigma.desc φ) := by
  classical
  let D := SectionCover.projectiveCoordinateSectionCover I
  have hfinite (i : Fin (n + 1)) : Module.Finite Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), D.opens i) Γ(M, D.opens i) :=
    Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M ⟨D.opens i, D.affine i⟩
  have hg (i : Fin (n + 1)) : ∃ (k : ℕ) (s : Fin k → Γ(M, D.opens i)),
      Submodule.span Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), D.opens i) (Set.range s) = ⊤ := by
    have := hfinite i
    exact Module.Finite.exists_fin
  choose k s hs using hg
  let ι := ULift.{u} (Σ i : Fin (n + 1), Fin (k i))
  have hmaps (a : ι) := NegativeTwistMorphisms.projective_quasicoherent_exists_negativeTwist_morphism I M a.down.1
    (s a.down.1 a.down.2)
  choose d φ hφ using hmaps
  refine ⟨ι, inferInstance, d, φ, ?_⟩
  apply HilbertConstruction.Module.EpimorphismCover.module_epi_of_affine_cover_section_surjective D.opens D.covers D.affine
  intro j
  apply HilbertConstruction.Module.CoproductSectionSurjection.module_coproduct_desc_section_surjective
    (fun a : ι => (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (d a)).sheaf) φ (D.opens j) (s j) (hs j)
  intro b
  let a : ι := ULift.up ⟨j, b⟩
  refine ⟨a, (ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I (d a)).reciprocal).frame
    (D.opens j) (ULift.up j) le_rfl 1, ?_⟩
  exact hφ a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistGeneration
