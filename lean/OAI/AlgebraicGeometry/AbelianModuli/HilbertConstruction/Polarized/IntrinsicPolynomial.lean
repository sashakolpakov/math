import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.SectionPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Intrinsic Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Polarized isomorphisms preserve the actual spaces of sections of every power of the canonical graph bundle, and hence its intrinsic Hilbert polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))}

def Moduli.Isomorphisms.LevelPreservingIso.graphPowerSectionsIso (e : Moduli.Isomorphisms.LevelPreservingIso A B) (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor B.abelian.scheme.hom).obj (B.graphBundle.tensorPower d).sheaf ≃ₗ[K]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj (A.graphBundle.tensorPower d).sheaf :=
  Intrinsic.LineBundleSections.lineBundlePowerSectionsOverIso e.abelian B.graphBundle A.graphBundle e.graphBundleIso d

theorem Moduli.Isomorphisms.LevelPreservingIso.graphBundle_sectionHilbertPolynomial_iff
    (e : Moduli.Isomorphisms.LevelPreservingIso A B) (P : Polynomial ℚ) :
    B.graphBundle.HasSectionHilbertPolynomial B.abelian.scheme.hom P ↔
      A.graphBundle.HasSectionHilbertPolynomial A.abelian.scheme.hom P :=
  Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sectionIso _ _ _ _ P e.graphPowerSectionsIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
