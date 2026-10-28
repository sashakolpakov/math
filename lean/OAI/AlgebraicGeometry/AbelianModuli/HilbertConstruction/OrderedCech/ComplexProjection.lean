import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.FormalProjection

/-! # Complex Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ComplexProjection

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem coefficientCechComplex_d_eq_sum_cofaces
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        FormalProjection.coefficientCechCoface ρ M U n k := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj
      (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ n).trans rfl

theorem coefficientCechComplex_d_comp_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).d n (n + 1) ≫
        Pi.π (fun j : Fin (n + 2) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U (n + 1) j) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (Pi.π (fun j : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map
            (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) := by
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U (n + 1) j) i
  change (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).d n (n + 1) ≫ p = _
  rw [coefficientCechComplex_d_eq_sum_cofaces, sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [zsmul_comp, FormalProjection.coefficientCechCoface_comp_π]
  rfl

theorem coefficientCechComplex_d_comp_coefficientCechToOrderedF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).d n (n + 1) ≫
        FormalProjection.coefficientCechToOrderedF ρ M U (n + 1) =
      FormalProjection.coefficientCechToOrderedF ρ M U n ≫
        Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential ρ M U n := by
  rw [coefficientCechComplex_d_eq_sum_cofaces,
    Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential, sum_comp, comp_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zsmul_comp, comp_zsmul,
    FormalProjection.coefficientCechCoface_comp_coefficientCechToOrderedF]

/-- The canonical projection from native Cech cochains to ordered Cech cochains. -/
noncomputable def coefficientCechToOrdered
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex ρ M U :=
  CochainComplex.ofHom (FormalProjection.coefficientCechToOrderedF ρ M U) fun n => by
    rw [Ordered.CoefficientCechComplex.orderedCoefficientCechComplex_d]
    exact (coefficientCechComplex_d_comp_coefficientCechToOrderedF ρ M U n).symm

@[simp]
theorem coefficientCechToOrdered_f
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (coefficientCechToOrdered ρ M U).f n = FormalProjection.coefficientCechToOrderedF ρ M U n :=
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ComplexProjection
