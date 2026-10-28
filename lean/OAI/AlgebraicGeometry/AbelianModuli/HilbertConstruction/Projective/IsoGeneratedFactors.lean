import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentGlobalGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LineBundleSectionFiniteness

/-! # Iso Generated Factors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IsoGeneratedFactors

noncomputable section

/-! Two generated factors for any actual line bundle on a scheme isomorphic to a projective quotient. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundle_two_generated_factors_of_projectiveIso
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (e : X ≅ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (L : Line.Bundles.LineBundle X) :
    ∃ H : Line.Bundles.LineBundle X, Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators H.sheaf ∧
      Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (L.tensor H).sheaf := by
  let M := L.pullback e.inv
  have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
  have : M.sheaf.IsFiniteType := M.isFiniteType
  obtain ⟨B, hB⟩ := CoherentGlobalGeneration.projective_finiteType_eventually_hasFiniteGlobalGenerators I M.sheaf
  let d := max B 1
  let P := ProjectiveTwisting.Bundle.projectiveTwistingBundle I d
  let H := P.pullback e.hom
  have hP : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators P.sheaf :=
    TwistGlobalGeneration.projectiveTwistingBundle_positive_hasFiniteGlobalGenerators I d
      (lt_of_lt_of_le Nat.zero_lt_one (le_max_right B 1))
  have hMP : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (M.tensor P).sheaf := hB d (le_max_left B 1)
  let eM : (M.pullback e.hom).sheaf ≅ L.sheaf :=
    (Scheme.Modules.pullbackComp e.hom e.inv).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr e.hom_inv_id).app L.sheaf ≪≫
        (Scheme.Modules.pullbackId X).app L.sheaf
  refine ⟨H, hP.pullback e.hom, ?_⟩
  exact (hMP.pullback e.hom).of_iso
    (Line.Bundles.LineBundle.tensorPullbackIso e.hom M P ≪≫
      Tensor.ProductSheaf.tensorModuleCongr eM (Iso.refl H.sheaf))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IsoGeneratedFactors
