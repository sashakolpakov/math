import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionConeRefinement

/-! # Section Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionRefinement.BoundedSectionRawRefinement

noncomputable section

/-! Refinement preserves the original bounded section edge.
Reuse the checked target presentation of the same reindexing map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w s t
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type v} [Category.{w} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (G : C ⥤ D) (F : D ⥤ Y.Opens) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G]
  (r : FormalCoproduct.mk ι (G.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex fY n I
local notation "M" => Functor.obj (OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.global (TopologicalSpace.Opens Y)) Q

def map := SectionConeRefinement.BoundedSectionConeRefinement.refinement fY n I G F U V r

theorem component (q : ℕ) : (SectionConeRefinement.BoundedSectionConeRefinement.oldEdge fY n I F V).f q ≫
    (map fY n I G F U V r).f q = (SectionConeRefinement.BoundedSectionConeRefinement.newEdge fY n I G F U).f q := by
  have result := SectionConeRefinement.BoundedSectionConeRefinement.component fY n I G F U V r q
  exact result

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionRefinement.BoundedSectionRawRefinement
