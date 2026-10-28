import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.SectionCechIndices
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Coefficient Cech Terms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechTerms

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace

universe u

abbrev coefficientCechFactor {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :=
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)))

/-- A term of the ordered base-linear Cech complex. -/
abbrev orderedCoefficientCechTerm {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (M : X.Modules) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) :=
  ∀ i : SectionCechIndices.OrderedCechIndex ι n, coefficientCechFactor c M U n i.1

/-- Ordered Cech cochains as a module over global functions on the base. -/
noncomputable def orderedCoefficientCechObject
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    ModuleCat.{u} R :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} R)).obj
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c M)).obj (op (SectionCechIndices.orderedCechFormalObject U n))

/-- Ordered Cech cochains are the concrete dependent product of their
intersection-section factors. -/
noncomputable def orderedCoefficientCechObjectIsoPi
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedCoefficientCechObject c M U n ≅
      ModuleCat.of R (orderedCoefficientCechTerm c M U n) :=
  ModuleCat.piIsoPi _

/-- The `k`th ordered Cech coface. -/
noncomputable def orderedCoefficientCechCoface
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    orderedCoefficientCechObject c M U n ⟶
      orderedCoefficientCechObject c M U (n + 1) :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} R)).obj
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c M)).map (SectionCechIndices.orderedCechFace U n k).op

theorem orderedCoefficientCechCoface_comp_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (k : Fin (n + 2)) (i : SectionCechIndices.OrderedCechIndex ι (n + 1)) :
    orderedCoefficientCechCoface c M U n k ≫
        Pi.π (fun j : SectionCechIndices.OrderedCechIndex ι (n + 1) =>
          coefficientCechFactor c M U (n + 1) j.1) i =
      Pi.π (fun j : SectionCechIndices.OrderedCechIndex ι n =>
        coefficientCechFactor c M U n j.1) (i.delete k) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op := by
  change (Pi.lift fun j : SectionCechIndices.OrderedCechIndex ι (n + 1) =>
      Pi.π (fun l : SectionCechIndices.OrderedCechIndex ι n =>
        coefficientCechFactor c M U n l.1) (j.delete k) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ j.1).op) ≫ _ = _
  exact Pi.lift_comp_π _ i

theorem orderedCoefficientCechCoface_comp
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    {i j : Fin (n + 2)} (hij : i ≤ j) :
    orderedCoefficientCechCoface c M U n i ≫
        orderedCoefficientCechCoface c M U (n + 1) j.succ =
      orderedCoefficientCechCoface c M U n j ≫
        orderedCoefficientCechCoface c M U (n + 1) i.castSucc := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} R :=
    ((FormalCoproduct.evalOp.{u} X.Opens
      (ModuleCat.{u} R)).obj
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c M))
  change F.map (SectionCechIndices.orderedCechFace U n i).op ≫
      F.map (SectionCechIndices.orderedCechFace U (n + 1) j.succ).op =
    F.map (SectionCechIndices.orderedCechFace U n j).op ≫
      F.map (SectionCechIndices.orderedCechFace U (n + 1) i.castSucc).op
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
    SectionCechIndices.orderedCechFace_comp U n hij]

theorem orderedCoefficientCechCoface_comp'
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    {i : Fin (n + 3)} {j : Fin (n + 2)} (hij : i ≤ j.castSucc) :
    orderedCoefficientCechCoface c M U n
          (i.castLT (lt_of_le_of_lt hij j.is_lt)) ≫
        orderedCoefficientCechCoface c M U (n + 1) j.succ =
      orderedCoefficientCechCoface c M U n j ≫
        orderedCoefficientCechCoface c M U (n + 1) i := by
  have hle : i.castLT (lt_of_le_of_lt hij j.is_lt) ≤ j := by
    rw [Fin.le_iff_val_le_val] at hij ⊢
    exact hij
  simpa using orderedCoefficientCechCoface_comp c M U n hle

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechTerms
