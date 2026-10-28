import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionCompositionRows

/-! # Section Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionComposition

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Lifting support-nonincreasing tuple maps reverses their composition. -/
theorem coefficientCechTupleMapF_comp
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (f : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
    (g : FreeCech.TupleChains.CechTupleChain ι m →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι l)
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f)
    (hg : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U (g.comp f)
        (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.comp hg hf) =
      SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
        SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf := by
  apply SectionIdentity.coefficientCechHom_ext coefficientMap M U n
  intro i
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i
  calc
    SectionMaps.coefficientCechTupleMapF coefficientMap M U (g.comp f)
          (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.comp hg hf) ≫ p =
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U (g.comp f)
          (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.comp hg hf) i := by
      dsimp only [p]
      exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U (g.comp f)
        (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.comp hg hf) i
    _ = SectionRows.coefficientCechTupleRow coefficientMap M U i
        (g (f (Finsupp.single i 1))) := rfl
    _ = SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
        SectionRows.coefficientCechTupleRow coefficientMap M U i
          (f (Finsupp.single i 1)) :=
      (SectionCompositionRows.coefficientCechTupleMapF_comp_row coefficientMap M U g hg i
        (f (Finsupp.single i 1)) (hf i)).symm
    _ = SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U f hf i := rfl
    _ = SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
        (SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf ≫ p) := by
      dsimp only [p]
      rw [SectionMaps.coefficientCechTupleMapF_comp_π]
    _ = (SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
          SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf) ≫ p :=
      (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionComposition
