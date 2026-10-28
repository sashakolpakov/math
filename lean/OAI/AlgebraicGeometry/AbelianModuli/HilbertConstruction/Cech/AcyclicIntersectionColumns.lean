import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveResolutionSectionExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CochainExactness

/-! # Acyclic Intersection Columns -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicIntersectionColumns.IntrinsicCech

noncomputable section

/-! Acyclic tuple intersections make the positive columns of the actual injective-resolution Čech double complex exact. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

def CechIntersectionsAcyclic
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ),
    Subsingleton (CategoryTheory.Sheaf.H
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat
        (∏ᶜ fun k : Fin (p + 1) => U (i k)).isOpenEmbedding).obj F) (q + 1))

theorem cechInjectiveResolution_columns_exactAt_succ
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hH : CechIntersectionsAcyclic U F) (p q : ℕ) :
    ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).flip.X p).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)]
  let I : InjectiveResolution F := injectiveResolution F
  let S := AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex I.cocomplex q
  change (S.map (CochainExactness.IntrinsicCech.cechCochainFunctor U p)).Exact
  apply CochainExactness.IntrinsicCech.cechCochainFunctor_exact_of_sections
  intro i x hx
  exact InjectiveResolutionSectionExactness.IntrinsicCech.injectiveResolution_sections_exact_succ F _ (hH p i) q x hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicIntersectionColumns.IntrinsicCech
