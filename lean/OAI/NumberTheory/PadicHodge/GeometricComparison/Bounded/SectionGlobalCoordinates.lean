import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionConeRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CechConeGlobal

/-! # Section Global Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionGlobalCoordinates.BoundedSectionGlobalCoordinates

noncomputable section

/-! The flasque and original bounded-section presentations give the
same global Čech edge, degree by degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type v} [Category.{w} C] [HasBinaryProducts C]
  (F : C ⥤ Y.Opens) {ι : Type} (U : ι → C)

theorem component (q : ℕ) : (CechConeGlobal.BoundedCechConeGlobalComparison.map fY n I F U).f q =
    (SectionConeRefinement.BoundedSectionConeRefinement.oldEdge fY n I F U).f q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionGlobalCoordinates.BoundedSectionGlobalCoordinates
