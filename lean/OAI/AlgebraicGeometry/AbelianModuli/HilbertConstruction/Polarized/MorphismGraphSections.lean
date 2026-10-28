import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismGraphBundleSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IntrinsicPolynomial

/-! # Morphism Graph Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual graphs of polarized isomorphisms have common intrinsic tensor-power section spaces, computed from the source canonical graph bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))}

def Moduli.Isomorphisms.LevelPreservingIso.morphismGraphPowerSectionsIso (e : Moduli.Isomorphisms.LevelPreservingIso A B) (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (MorphismGraphFamilies.morphismGraphFamily e.abelian.hom).scheme.hom).obj
      ((MorphismGraphBundleSections.morphismGraphExternalBundle e.abelian.hom A.graphBundle B.graphBundle).tensorPower d).sheaf ≃ₗ[K]
        (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
          ((A.graphBundle.tensor A.graphBundle).tensorPower d).sheaf :=
  MorphismGraphBundleSections.morphismGraphPowerSectionsIsoOfPreserves e.abelian.hom A.graphBundle B.graphBundle e.graphBundleIso d

theorem Moduli.Isomorphisms.LevelPreservingIso.morphismGraph_sectionHilbertPolynomial_iff
    (e : Moduli.Isomorphisms.LevelPreservingIso A B) (P : Polynomial ℚ) :
    (MorphismGraphBundleSections.morphismGraphExternalBundle e.abelian.hom A.graphBundle B.graphBundle).HasSectionHilbertPolynomial
      (MorphismGraphFamilies.morphismGraphFamily e.abelian.hom).scheme.hom P ↔
        (A.graphBundle.tensor A.graphBundle).HasSectionHilbertPolynomial A.abelian.scheme.hom P :=
  Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sectionIso _ _ _ _ P e.morphismGraphPowerSectionsIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
