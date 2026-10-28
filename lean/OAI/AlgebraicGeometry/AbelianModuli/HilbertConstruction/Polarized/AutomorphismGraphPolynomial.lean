import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ExternalSquareEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Ampleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.MorphismGraphSections

/-! # Automorphism Graph Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A constructed projective embedding of the external square of the canonical polarized bundle gives one actual graph Hilbert polynomial for every polarized full-level automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

def PolarizationData.PolarizedAbelianWithFullLevel.automorphismGraphPowerEmbedding :
    Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle A.graphBundle A.graphBundle)
      (A.abelian.scheme ⊗ A.abelian.scheme).hom :=
  Ample.ExternalSquareEmbedding.ampleExternalSquarePowerEmbedding (A := A.abelian.scheme) A.graphBundle A.graphBundle_isAmple_overAlgClosed

def PolarizationData.PolarizedAbelianWithFullLevel.automorphismGraphPolynomial : Polynomial ℚ :=
  Classical.choose (A.automorphismGraphPowerEmbedding.exists_common_graphHilbertPolynomial A.graphBundle)

theorem PolarizationData.PolarizedAbelianWithFullLevel.automorphismGraphPolynomial_spec (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      (A.automorphismGraphPowerEmbedding.relativeMorphism A.graphBundle A.graphBundle)
      A.automorphismGraphPolynomial e.abelian.hom :=
  Classical.choose_spec (A.automorphismGraphPowerEmbedding.exists_common_graphHilbertPolynomial A.graphBundle)
    e.abelian.hom ⟨e.graphBundleIso⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
