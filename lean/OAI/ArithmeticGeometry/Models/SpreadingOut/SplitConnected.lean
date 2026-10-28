import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitProper

/-! # Split Connected -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SplitConnected.Construction

noncomputable section

/-! Models can preserve geometric connectedness for the objects that have
it, while retaining split geometric components for every object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem hasSplitGeometricComponents_of_geometricallyConnected
    {S : Scheme.{u}} (M : Over S) [GeometricallyConnected M.hom] :
    Base.Construction.HasSplitGeometricComponents M := by
  refine ⟨1, (fun _ ↦ ⊤), ?_, ?_, ?_⟩
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · simp
  · intro i
    have : IsIso (⊤ : M.left.Opens).ι := inferInstanceAs (IsIso M.left.topIso.hom)
    have h : IsPullback (⊤ : M.left.Opens).ι
        ((⊤ : M.left.Opens).ι ≫ M.hom) M.hom (𝟙 S) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    exact MorphismProperty.of_isPullback h inferInstance

theorem split_connected_smooth_proper_has_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsProper X.hom]
    (hX : Base.Construction.HasSplitGeometricComponents X) :
    ∃ N : Foundations.Constructions.CoefficientModel K X,
      Smooth N.model.hom ∧ IsProper N.model.hom ∧ Base.Construction.HasSplitGeometricComponents N.model ∧
      (GeometricallyConnected X.hom → GeometricallyConnected N.model.hom) := by
  classical
  by_cases hc : GeometricallyConnected X.hom
  · have : GeometricallyConnected X.hom := hc
    have : GeometricallyIrreducible X.hom :=
      SmoothGeometricIntegrality.Construction.smooth_proper_geometricallyConnected_is_geometricallyIrreducible X.hom
    obtain ⟨N, hs, hp, hi⟩ := GeometricProper.Construction.smooth_proper_geometricallyIrreducible_has_coefficient_model X
    have : GeometricallyIrreducible N.model.hom := hi
    have hN : GeometricallyConnected N.model.hom :=
      SplitCoproducts.Construction.geometricallyConnected_of_geometricallyIrreducible N.model.hom
    exact ⟨N, hs, hp, hasSplitGeometricComponents_of_geometricallyConnected N.model, fun _ ↦ hN⟩
  · obtain ⟨N, hs, hp, hi⟩ := SplitProper.Construction.split_smooth_proper_has_coefficient_model X hX
    exact ⟨N, hs, hp, hi, fun h ↦ (hc h).elim⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SplitConnected.Construction
