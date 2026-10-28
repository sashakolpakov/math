import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap

/-! # Diagram Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComposition

noncomputable section

/-!
# IntegralComparison: identity and composition for the actual relative crystalline complex maps
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramFormMap

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H K L Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q) (σ : L ⟶ Q)

theorem forms_id (U : C) (n : ℕ) (ω : RelativeCrystalline.FormData.Forms H Q π U n) :
    DiagramFormMap.map H H Q π π (𝟙 H) (Category.id_comp π) U n ω = ω := by
  let : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_id
    (A := CommAlgCat.of (Q.obj U).ring (H.obj U).ring)
    (DividedPowers.DPMorphism.id (H.obj U).dividedPowers).isDPMorphism n ω

theorem complex_id : DiagramComplexMap.map H H Q π π (𝟙 H) (Category.id_comp π) =
    𝟙 (RelativeCrystalline.ModuleComplex.complex H Q π) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact forms_id H Q π U.unop n ω

variable (θ : H ⟶ K) (τ : K ⟶ L) (hθ : θ ≫ ρ = π) (hτ : τ ≫ σ = ρ)

include hθ hτ in
theorem triangle : (θ ≫ τ) ≫ σ = π :=
  (Category.assoc θ τ σ).trans ((congrArg (fun t => θ ≫ t) hτ).trans hθ)

theorem forms_comp (U : C) (n : ℕ) (ω : RelativeCrystalline.FormData.Forms L Q σ U n) :
    DiagramFormMap.map H L Q π σ (θ ≫ τ) (triangle H K L Q π ρ σ θ τ hθ hτ) U n ω =
      DiagramFormMap.map H K Q π ρ θ hθ U n (DiagramFormMap.map K L Q ρ σ τ hτ U n ω) := by
  let : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  let : Algebra (Q.obj U).ring (K.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U
  let : Algebra (Q.obj U).ring (L.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra L Q σ U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_comp
    (CommAlgCat.ofHom (DiagramFormMap.algebraMap K L Q ρ σ τ hτ U)) (CommAlgCat.ofHom (DiagramFormMap.algebraMap H K Q π ρ θ hθ U))
    (τ.app U).ringMap.isDPMorphism (θ.app U).ringMap.isDPMorphism
    ((θ ≫ τ).app U).ringMap.isDPMorphism n ω

theorem complex_comp :
    DiagramComplexMap.map H L Q π σ (θ ≫ τ) (triangle H K L Q π ρ σ θ τ hθ hτ) =
      DiagramComplexMap.map K L Q ρ σ τ hτ ≫ DiagramComplexMap.map H K Q π ρ θ hθ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact forms_comp H K L Q π ρ σ θ τ hθ hτ U.unop n ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComposition
