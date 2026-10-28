import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.SectionTranspose
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LineBundleSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.SectionsFinite

/-! # Line Bundle Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LineBundleSectionFiniteness

noncomputable section

/-! Every actual line bundle on a homogeneous projective quotient over a Noetherian ring has a finite module of global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projective_lineBundle_sections_finite (L : Line.Bundles.LineBundle (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj L.sheaf) := by
  have := L.reciprocalFrameBundle.isQuasicoherent
  have := L.reciprocalFrameBundle.isFiniteType
  obtain ⟨ι, hι, d, φ, hepi⟩ :=
    NegativeTwistGeneration.projective_quasicoherent_finiteType_negativeTwist_quotient I L.reciprocalFrameBundle.sheaf
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
  let A := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf
  let B (i : ι) := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (ProjectiveTwisting.Bundle.projectiveTwistingBundle I (d i)).sheaf
  have hfinite (i : ι) : Module.Finite R (B i) := ProjectiveTwisting.SectionsFinite.projectiveTwistingSections_finite I (d i)
  let a : A →ₗ[R] (∀ i : ι, B i) :=
    LinearMap.pi (fun i => NegativeTwist.SectionTranspose.negativeTwistSectionTranspose I L.sectionPairing (d i) (φ i))
  have ha : Function.Injective a := by
    intro s t hst
    have hz : a (s - t) = 0 := by rw [map_sub, hst, sub_self]
    have hc : L.sectionPairing.contractLeft (s - t) = 0 := by
      apply (cancel_epi (Sigma.desc φ)).mp
      rw [comp_zero]
      apply Sigma.hom_ext
      intro i
      rw [Sigma.ι_comp_desc_assoc, comp_zero]
      exact NegativeTwist.SectionTranspose.negativeTwistSectionTranspose_zero_implies I L.sectionPairing (d i) (φ i) (s - t)
        (congrFun hz i)
    have he : (s - t : A) = 0 :=
      L.sectionPairing_contractLeft_injective (hc.trans L.sectionPairing.contractLeft_zero.symm)
    exact sub_eq_zero.mp he
  have : Module.Finite R (∀ i : ι, B i) := inferInstance
  exact Module.Finite.of_injective a ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LineBundleSectionFiniteness
