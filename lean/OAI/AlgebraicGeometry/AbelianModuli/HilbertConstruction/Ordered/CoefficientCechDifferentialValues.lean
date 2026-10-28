import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex

/-! # Coefficient Cech Differential Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechDifferentialValues

noncomputable section

/-! The actual coefficient Čech differential evaluates as the alternating sum of restricted components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

theorem orderedCoefficientCechDifferential_value (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (q : ℕ)
    (a : SectionCechIndices.OrderedCechIndex ι (q + 1)) (x : CoefficientCechTerms.orderedCoefficientCechObject c M U q) :
    Pi.π (fun b : SectionCechIndices.OrderedCechIndex ι (q + 1) ↦ CoefficientCechTerms.coefficientCechFactor c M U (q + 1) b.val) a
      (CoefficientCechComplex.orderedCoefficientCechDifferential c M U q x) =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map
          (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op
          (Pi.π (fun b : SectionCechIndices.OrderedCechIndex ι q ↦ CoefficientCechTerms.coefficientCechFactor c M U q b.val) (a.delete k) x) := by
  let A : ModuleCat.{u} R := CoefficientCechTerms.orderedCoefficientCechObject c M U q
  let B : ModuleCat.{u} R := CoefficientCechTerms.coefficientCechFactor c M U (q + 1) a.val
  let ev : (A ⟶ B) →+ B :=
    { toFun := fun f ↦ f.hom x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let t (k : Fin (q + 2)) : A ⟶ B :=
    Pi.π (fun b : SectionCechIndices.OrderedCechIndex ι q ↦ CoefficientCechTerms.coefficientCechFactor c M U q b.val) (a.delete k) ≫
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map
        (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op
  have h := congrArg ev (CoefficientCechComplex.orderedCoefficientCechDifferential_comp_π c M U q a)
  have hs : ev (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • t k) =
      ∑ k : Fin (q + 2), ev ((-1 : ℤ) ^ k.val • t k) := map_sum ev _ _
  have hz : (∑ k : Fin (q + 2), ev ((-1 : ℤ) ^ k.val • t k)) =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • ev (t k) :=
    Finset.sum_congr rfl (fun k _ ↦ map_zsmul ev ((-1 : ℤ) ^ k.val) (t k))
  exact h.trans (hs.trans hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechDifferentialValues
