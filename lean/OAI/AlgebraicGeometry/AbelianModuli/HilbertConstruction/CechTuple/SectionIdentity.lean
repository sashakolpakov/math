import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SupportFunctoriality

/-! # Section Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionIdentity

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Extensionality for a map into one native base-Cech degree, using its concrete tuple factors. -/
theorem coefficientCechHom_ext
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    {A : ModuleCat.{u} R}
    {f g : A ⟶ (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n}
    (h : ∀ i : Fin (n + 1) → ι,
      f ≫ Pi.π (fun q : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i =
        g ≫ Pi.π (fun q : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i) :
    f = g := by
  apply (cancel_mono (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi coefficientMap M U n).hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi := h i
  have hcomp :
      (f ≫ (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi coefficientMap M U n).hom) ≫
          ModuleCat.ofHom
            (LinearMap.proj i :
              (∀ q : Fin (n + 1) → ι,
                Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) →ₗ[
                  R]
                Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i) =
        (g ≫ (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi coefficientMap M U n).hom) ≫
          ModuleCat.ofHom
            (LinearMap.proj i :
              (∀ q : Fin (n + 1) → ι,
                Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) →ₗ[
                  R]
                Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i) := by
    simpa only [Category.assoc, CoefficientCech.Permutations.coefficientCechXIsoPi_hom_comp_proj]
      using hi
  exact ConcreteCategory.congr_hom hcomp x

/-- The lift of the identity tuple-chain map is the identity on Cech cochains. -/
theorem coefficientCechTupleMapF_id
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U
        (LinearMap.id :
          FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι n)
        SupportFunctoriality.cechTupleSupportNonincreasing_id =
      𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n := by
  apply coefficientCechHom_ext coefficientMap M U n
  intro i
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i
  calc
    SectionMaps.coefficientCechTupleMapF coefficientMap M U LinearMap.id
          SupportFunctoriality.cechTupleSupportNonincreasing_id ≫ p =
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U LinearMap.id
          SupportFunctoriality.cechTupleSupportNonincreasing_id i := by
      dsimp only [p]
      exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U
        LinearMap.id SupportFunctoriality.cechTupleSupportNonincreasing_id i
    _ = p := by
      change SectionRows.coefficientCechTupleRow coefficientMap M U i (Finsupp.single i 1) = p
      rw [SectionRows.coefficientCechTupleRow_single_of_subset
        coefficientMap M U i i 1 Subset.rfl, one_zsmul,
        SectionRestrictions.coefficientCechTupleRestriction_self]
      simp [p]
      rfl
    _ = 𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ≫ p :=
      (Category.id_comp p).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionIdentity
