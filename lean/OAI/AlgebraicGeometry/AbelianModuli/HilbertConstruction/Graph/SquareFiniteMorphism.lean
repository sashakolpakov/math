import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.SquareFieldGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeometricallyAmpleSectionMorphism

/-! # Square Finite Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Any generating family for the graph-bundle square defines a finite
projective-space morphism, with the actual square as its pulled-back O(1). -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_sectionMap_isFinite
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left := by
  apply GeometricallyAmpleSectionMorphism.sectionProjectiveMorphism_isFinite_of_geometric_ample A.abelian.scheme.hom
    (A.graphBundle.tensorPower 2) s hs
  intro K _ _ f
  exact ((A.graphBundle_ample_geometricFiber K f).tensorPower 2 (by decide)).of_iso
    (A.graphBundle.powerBaseChangeIso (CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom f) 2).symm

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_exists_finite_square_sectionMap
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∃ (n : ℕ) (s : Fin (n + 1) →
        (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf))
      (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)),
      IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left := by
  obtain ⟨n, s, hs⟩ := A.graphBundle_square_finite_section_cover_overField hN hNk
  exact ⟨n, s, hs, A.graphBundle_square_sectionMap_isFinite s hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
