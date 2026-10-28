import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.FiniteCoproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LineBundleSectionFiniteness

/-! # Negative Twist Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistCover

noncomputable section

/-! The constructed finite negative-twist quotient, recorded with its actual maps and epimorphism proof. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

structure ProjectiveNegativeTwistCover (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules) where
  index : Type u
  finite : Finite index
  degree : index → ℕ
  component : ∀ i, (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (degree i)).sheaf ⟶ M
  epi : Epi (Sigma.desc component)

namespace ProjectiveNegativeTwistCover

variable {I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)} {M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules}

def ofFiniteType (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : ProjectiveNegativeTwistCover I M := by
  rename_i hMq hMt
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let : M.IsQuasicoherent := hMq
  let : M.IsFiniteType := hMt
  apply Classical.choice
  obtain ⟨ι, hι, d, φ, hφ⟩ := NegativeTwistGeneration.projective_quasicoherent_finiteType_negativeTwist_quotient I M
  exact ⟨⟨ι, hι, d, φ, hφ⟩⟩

def source (D : ProjectiveNegativeTwistCover I M) : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules :=
  ∐ fun i : D.index ↦ (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (D.degree i)).sheaf

def projection (D : ProjectiveNegativeTwistCover I M) : D.source ⟶ M := Sigma.desc D.component

theorem projection_epi (D : ProjectiveNegativeTwistCover I M) : Epi D.projection := D.epi

theorem source_quasicoherent (D : ProjectiveNegativeTwistCover I M) : D.source.IsQuasicoherent :=
  Quasicoherent.Coproducts.module_quasicoherent_coproduct _ (fun i ↦ Line.Bundles.LineBundle.isQuasicoherent
    (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (D.degree i)))

theorem source_finiteType (D : ProjectiveNegativeTwistCover I M) : D.source.IsFiniteType := by
  let : Finite D.index := D.finite
  exact Quasicoherent.FiniteCoproducts.module_finiteType_finite_coproduct _
    (fun i ↦ Line.Bundles.LineBundle.isQuasicoherent (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (D.degree i)))
    (fun i ↦ Line.Bundles.LineBundle.isFiniteType (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I (D.degree i)))

end ProjectiveNegativeTwistCover

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistCover
