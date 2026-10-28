import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionIdentity

/-! # Section Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionAdditivity

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- The restriction lift is additive in the tuple-chain map. -/
theorem coefficientCechTupleMapF_add
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f g : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f)
    (hg : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U (f + g)
        (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.add hf hg) =
      SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf +
        SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg := by
  apply SectionIdentity.coefficientCechHom_ext coefficientMap M U n
  intro i
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i
  calc
    SectionMaps.coefficientCechTupleMapF coefficientMap M U (f + g)
          (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.add hf hg) ≫ p =
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U (f + g)
          (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.add hf hg) i := by
      dsimp only [p]
      exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U
        (f + g) (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.add hf hg) i
    _ = SectionMaps.coefficientCechTupleMapComponent coefficientMap M U f hf i +
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U g hg i := by
      change SectionRows.coefficientCechTupleRow coefficientMap M U i
          ((f + g) (Finsupp.single i 1)) =
        SectionRows.coefficientCechTupleRow coefficientMap M U i (f (Finsupp.single i 1)) +
          SectionRows.coefficientCechTupleRow coefficientMap M U i (g (Finsupp.single i 1))
      simp
    _ = (SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf ≫ p) +
        (SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫ p) := by
      dsimp only [p]
      rw [SectionMaps.coefficientCechTupleMapF_comp_π,
        SectionMaps.coefficientCechTupleMapF_comp_π]
    _ = (SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf +
          SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg) ≫ p :=
      by rw [add_comp]

/-- The restriction lift sends negation to negation. -/
theorem coefficientCechTupleMapF_neg
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U (-f)
        (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.neg hf) =
      -SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf := by
  apply SectionIdentity.coefficientCechHom_ext coefficientMap M U n
  intro i
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i
  calc
    SectionMaps.coefficientCechTupleMapF coefficientMap M U (-f)
          (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.neg hf) ≫ p =
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U (-f)
          (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.neg hf) i := by
      dsimp only [p]
      exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U (-f)
        (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.neg hf) i
    _ = -SectionMaps.coefficientCechTupleMapComponent coefficientMap M U f hf i := by
      change SectionRows.coefficientCechTupleRow coefficientMap M U i
          ((-f) (Finsupp.single i 1)) =
        -SectionRows.coefficientCechTupleRow coefficientMap M U i (f (Finsupp.single i 1))
      simp
    _ = -(SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf ≫ p) := by
      dsimp only [p]
      rw [SectionMaps.coefficientCechTupleMapF_comp_π]
    _ = (-SectionMaps.coefficientCechTupleMapF coefficientMap M U f hf) ≫ p :=
      by rw [neg_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionAdditivity
