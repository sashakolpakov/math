import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ComplexForget

/-! # Scalar Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ScalarMaps

noncomputable section

open _root_.AlgebraicTopology _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u

@[reassoc]
theorem coefficientCechComplexFunctor_map_f_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : (unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).I) :
    ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).map f).f n ≫
        Pi.π (fun j => ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).obj N).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i =
      Pi.π (fun j => ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).obj M).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i ≫
        ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f).app
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj i)) := by
  change Limits.Pi.map (fun j => ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f).app
      (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
        (SimplexCategory.mk n))).obj j))) ≫ _ = _
  exact Limits.Pi.map_π _ i

/-- A coefficient endomorphism that is scalar multiplication on every
base-linear section module induces scalar multiplication on the entire Cech
complex. -/
theorem coefficientCechComplexFunctor_map_eq_smul_id
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules) (f : M ⟶ M)
    {ι : Type u} (U : ι → X.Opens) (r : R)
    (h : ∀ V, ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f).app V =
      r • 𝟙 (((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).obj M).obj V)) :
    ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor ρ U).map f :
      Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U ⟶ Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U) =
      r • 𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U) := by
  let K := (cechComplexFunctor U).obj
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).obj M)
  change (cechComplexFunctor U).map
      ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f) = r • 𝟙 K
  apply HomologicalComplex.Hom.ext
  funext n
  let P := fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j
  let e : K.X n ≅ ModuleCat.of R (∀ j, P j) :=
    Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n
  apply (cancel_mono e.hom).1
  ext x
  rename_i i
  let p := Pi.π P i
  let proj := ModuleCat.ofHom
    (LinearMap.proj i : (∀ j, P j) →ₗ[R] P i)
  have he : e.hom ≫ proj = p := by
    exact ModuleCat.piIsoPi_hom_ker_subtype P i
  have hi := coefficientCechComplexFunctor_map_f_π ρ f U n i
  change ((cechComplexFunctor U).map
      ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f)).f n ≫ p =
    p ≫ ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f).app _ at hi
  rw [h] at hi
  change _ = p ≫ (r • 𝟙 (P i)) at hi
  erw [← he] at hi
  have hs : (r • 𝟙 (K.X n)) ≫ e.hom = r • e.hom := by
    simpa only [Category.id_comp] using
      Linear.smul_comp (K.X n) (K.X n) _ r (𝟙 (K.X n)) e.hom
  have hcat :
      ((((cechComplexFunctor U).map
          ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f)).f n ≫ e.hom) ≫ proj) =
        (((r • 𝟙 K).f n ≫ e.hom) ≫ proj) := by
    calc
      _ = ((cechComplexFunctor U).map
            ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f)).f n ≫
          (e.hom ≫ proj) := Category.assoc _ _ _
      _ = ((cechComplexFunctor U).map
            ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor ρ).map f)).f n ≫
          (e.hom ≫ proj) := rfl
      _ = (e.hom ≫ proj) ≫ (r • 𝟙 (P i)) := hi
      _ = e.hom ≫ (proj ≫ (r • 𝟙 (P i))) :=
        Category.assoc _ _ _
      _ = e.hom ≫ (r • proj) := by
        rw [Linear.comp_smul, Category.comp_id]
      _ = r • (e.hom ≫ proj) := by rw [Linear.comp_smul]
      _ = (r • e.hom) ≫ proj := by rw [Linear.smul_comp]
      _ = ((r • 𝟙 (K.X n)) ≫ e.hom) ≫ proj := by
        exact congrArg (fun q => q ≫ proj) hs.symm
      _ = (((r • 𝟙 K).f n ≫ e.hom) ≫ proj) := rfl
  exact ConcreteCategory.congr_hom hcat x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ScalarMaps
