import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite

/-! # Projective Cohomology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCohomology.Construction.ProjectiveCechComplex

noncomputable section

/-! Finite cohomology for the bounded affine Cech model of a projective scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X)

theorem finite (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite Γ(Spec (.of Γ(S, ⊤)), ⊤) ((ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P M).homology q) := by
  have := ProjectivePresentation.Construction.ProjectivePresentationEmbedding.closed X P
  exact SheafCohomology.Projective.TwistCechFinite.MvPolynomial.closedImmersion_finiteType_orderedBaseCechComplex_homology_module_finite
    (R := Γ(S, ⊤)) (σ := Fin (P.dimension + 1))
    (ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map X P) M q

theorem lineBundle_finite (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (q : ℕ) :
    Module.Finite Γ(Spec (.of Γ(S, ⊤)), ⊤) ((ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P L.sheaf).homology q) := by
  have : L.sheaf.IsFinitePresentation := LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  have : L.sheaf.IsQuasicoherent := LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFiniteType := by
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  exact finite X P L.sheaf q

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCohomology.Construction.ProjectiveCechComplex
