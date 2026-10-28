import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ProjectionCoordinates

/-! # Projection Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ProjectionSplitting

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem coefficientCechToOrderedF_concrete
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫ FormalProjection.coefficientCechToOrderedF ρ M U n ≫
        (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom =
      ModuleCat.ofHom (ProjectionCoordinates.coefficientCechPiToOrderedLinearMap ρ M U n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hcomp :
      ((Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫ FormalProjection.coefficientCechToOrderedF ρ M U n ≫
          (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom) ≫
          ModuleCat.ofHom (LinearMap.proj i) =
        ModuleCat.ofHom (ProjectionCoordinates.coefficientCechPiToOrderedLinearMap ρ M U n) ≫
          ModuleCat.ofHom (LinearMap.proj i) := by
    simp only [Category.assoc]
    rw [ProjectionCoordinates.orderedCoefficientCechObjectIsoPi_hom_comp_proj]
    rw [ProjectionCoordinates.coefficientCechToOrderedF_comp_π]
    rw [ProjectionCoordinates.coefficientCechXIsoPi_inv_comp_proj]
    ext y
    rfl
  exact ConcreteCategory.congr_hom hcomp x

/-- A degreewise section of the projection, obtained by zero extension. -/
noncomputable def orderedToCoefficientCechZeroExtensionF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    Ordered.CoefficientCechTerms.orderedCoefficientCechObject ρ M U n ⟶ (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X n :=
  (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom ≫
    ModuleCat.ofHom (ProjectionCoordinates.orderedCoefficientCechZeroExtendLinearMap ρ M U n) ≫
      (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv

theorem orderedToCoefficientCechZeroExtensionF_comp_coefficientCechToOrderedF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedToCoefficientCechZeroExtensionF ρ M U n ≫
      FormalProjection.coefficientCechToOrderedF ρ M U n = 𝟙 _ := by
  apply (cancel_mono (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom).1
  simp only [orderedToCoefficientCechZeroExtensionF, Category.id_comp,
    Category.assoc]
  rw [coefficientCechToOrderedF_concrete]
  change (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom ≫
      ModuleCat.ofHom ((ProjectionCoordinates.coefficientCechPiToOrderedLinearMap ρ M U n).comp
        (ProjectionCoordinates.orderedCoefficientCechZeroExtendLinearMap ρ M U n)) =
    (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom
  rw [ProjectionCoordinates.coefficientCechPiToOrderedLinearMap_comp_zeroExtend]
  simp

instance coefficientCechToOrderedF_epi
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    Epi (FormalProjection.coefficientCechToOrderedF ρ M U n) :=
  (SplitEpi.mk
    (orderedToCoefficientCechZeroExtensionF ρ M U n)
    (orderedToCoefficientCechZeroExtensionF_comp_coefficientCechToOrderedF ρ M U n)).epi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ProjectionSplitting
