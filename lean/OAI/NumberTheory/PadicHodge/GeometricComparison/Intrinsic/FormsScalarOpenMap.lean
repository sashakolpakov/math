import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionPullback

/-! # Forms Scalar Open Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarOpenMap.IntrinsicFormsScalarOpenMap

noncomputable section

/-! Scalar extension of native forms followed by restriction to any smaller open, with its formula on generators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (U : X.left.Opens) (V : Y.left.Opens) (hV : V ≤ f ⁻¹ᵁ U)

def component (n : ℕ) :
    (FlatScalar.FlatScalarExtension.moduleFunctor R S).obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U)) ⟶
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).obj (op V) :=
  FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h U n ≫ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).map (homOfLE hV).op

theorem component_tmul_symbol {n : ℕ} (s : S) (a : Γ(X.left, U)) (t : Fin n → Γ(X.left, U)) :
    component R S X Y f h U V hV n (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, U) a t) =
      s • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y.left, V) ((f.appLE U V hV) a) (fun i => (f.appLE U V hV) (t i)) := by
  let : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra S Γ(Y.left, V) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y V
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  let g : CommAlgCat.of S Γ(Y.left, f ⁻¹ᵁ U) ⟶ CommAlgCat.of S Γ(Y.left, V) :=
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras S Y).map (homOfLE hV).op
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap g n
    (Forms.ScalarMap.FormsBaseChange.formScalarMap R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n
      (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, U) a t)) = _
  rw [Forms.ScalarMap.FormsBaseChange.formScalarMap_tmul, map_smul, Forms.ScalarMap.FormsBaseChange.formExtensionMap_symbol,
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  rfl

theorem component_preimage (n : ℕ) : component R S X Y f h U (f ⁻¹ᵁ U) le_rfl n =
    FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h U n := by
  change FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h U n ≫ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).map (𝟙 _) = _
  rw [(AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).map_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarOpenMap.IntrinsicFormsScalarOpenMap
