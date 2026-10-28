import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicFormsScalarMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarHomExt
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback

/-! # Forms Scalar Open Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.FormsScalarOpenMap.BaseIntrinsicFormsScalarOpenMap

noncomputable section

/-! Scalar extension of native forms followed by restriction to any smaller open, with its formula on generators. -/

section

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (U : X.left.Opens) (V : Y.left.Opens) (hV : V ≤ f ⁻¹ᵁ U)

def component (n : ℕ) :
    (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).obj ((DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U)) ⟶
      (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).obj (op V) :=
  IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.component R S X Y f h U n ≫ (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).map (homOfLE hV).op

theorem component_tmul_symbol {n : ℕ} (s : S) (a : Γ(X.left, U)) (t : Fin n → Γ(X.left, U)) :
    component R S X Y f h U V hV n (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, U) a t) =
      s • DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y.left, V) ((f.appLE U V hV) a) (fun i => (f.appLE U V hV) (t i)) := by
  let : Algebra R Γ(X.left, U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra S Γ(Y.left, V) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y V
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceTower R S X Y f U h
  let g : CommAlgCat.of S Γ(Y.left, f ⁻¹ᵁ U) ⟶ CommAlgCat.of S Γ(Y.left, V) :=
    (AlgebraicForms.AlgebraicDeRham.sectionAlgebras S Y).map (homOfLE hV).op
  change DeRhamGlobalId.DeRhamGlobal.formMap g n
    (NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n
      (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X.left, U) a t)) = _
  rw [NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap_tmul, map_smul, NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap_symbol,
    DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  rfl

theorem component_preimage (n : ℕ) : component R S X Y f h U (f ⁻¹ᵁ U) le_rfl n =
    IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.component R S X Y f h U n := by
  change IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.component R S X Y f h U n ≫ (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).map (𝟙 _) = _
  rw [(DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).map_id, Category.comp_id]

end

/-! Scalar extension commutes with geometric pullback on all compatible open subsets of an actual commuting square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal
open scoped TensorProduct

universe u₀

variable (R S : Type u₀) [CommRing R] [CommRing S] [Algebra R S]
  {X₁ X₂ : Over (Spec (CommRingCat.of R))}
  {Y₁ Y₂ : Over (Spec (CommRingCat.of S))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (h₁ : f₁ ≫ X₁.hom = Y₁.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (h₂ : f₂ ≫ X₂.hom = Y₂.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  (U : X₂.left.Opens) (V : X₁.left.Opens) (W : Y₂.left.Opens) (T : Y₁.left.Opens)
  (hu : V ≤ u.left ⁻¹ᵁ U) (hv : T ≤ v.left ⁻¹ᵁ W)
  (hT : T ≤ f₁ ⁻¹ᵁ V) (hW : W ≤ f₂ ⁻¹ᵁ U)

include hsquare in
theorem geometric_naturality (n : ℕ) :
    (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).map (OpenSectionGeometricPullback.DeRhamPullback.formsPullbackLE u U V hu n) ≫
        component R S X₁ Y₁ f₁ h₁ V T hT n =
      component R S X₂ Y₂ f₂ h₂ U W hW n ≫ OpenSectionGeometricPullback.DeRhamPullback.formsPullbackLE v W T hv n := by
  let : Algebra R Γ(X₂.left, U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X₂ U
  let : Algebra R Γ(X₁.left, V) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X₁ V
  let : Algebra S Γ(Y₂.left, W) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y₂ W
  let : Algebra S Γ(Y₁.left, T) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y₁ T
  let aR : CommAlgCat.of R Γ(X₂.left, U) ⟶ CommAlgCat.of R Γ(X₁.left, V) :=
    CommAlgCat.ofHom (OpenSectionGeometricPullback.DeRhamPullback.sectionPullbackLE u U V hu)
  let aS : CommAlgCat.of S Γ(Y₂.left, W) ⟶ CommAlgCat.of S Γ(Y₁.left, T) :=
    CommAlgCat.ofHom (OpenSectionGeometricPullback.DeRhamPullback.sectionPullbackLE v W T hv)
  let gS : DeRhamPresentationTo.DeRhamPresentation.Form S Γ(Y₂.left, W) n →ₗ[S] DeRhamPresentationTo.DeRhamPresentation.Form S Γ(Y₁.left, T) n := DeRhamGlobalId.DeRhamGlobal.formMap aS n
  have hs := OpenSectionGeometricPullback.SectionGeometricSquare.square u.left v.left f₁ f₂ hsquare U V W T hu hv hT hW
  apply NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarHomExt.FormsHomExt.scalar_hom_ext R S Γ(X₂.left, U) n
  intro s a t
  have ha : (DeRhamGlobalId.DeRhamGlobal.formMap aR n).baseChange S (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t) =
      s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₁.left, V) (aR a) (fun i => aR (t i)) :=
    (LinearMap.baseChange_tmul (DeRhamGlobalId.DeRhamGlobal.formMap aR n) s _).trans
      (congrArg (fun ω => s ⊗ₜ[R] ω) (DeRhamGlobalId.DeRhamGlobal.formMap_symbol aR n a t))
  change component R S X₁ Y₁ f₁ h₁ V T hT n
      ((DeRhamGlobalId.DeRhamGlobal.formMap aR n).baseChange S (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t)) =
    gS (component R S X₂ Y₂ f₂ h₂ U W hW n (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t))
  have hb : gS (DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₂.left, W) ((f₂.appLE U W hW) a)
      (fun i => (f₂.appLE U W hW) (t i))) =
      DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) (aS ((f₂.appLE U W hW) a))
        (fun i => aS ((f₂.appLE U W hW) (t i))) := DeRhamGlobalId.DeRhamGlobal.formMap_symbol aS n _ _
  have hL : component R S X₁ Y₁ f₁ h₁ V T hT n
      ((DeRhamGlobalId.DeRhamGlobal.formMap aR n).baseChange S (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t)) =
      s • DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) ((f₁.appLE V T hT) (aR a))
        (fun i => (f₁.appLE V T hT) (aR (t i))) :=
    (congrArg (component R S X₁ Y₁ f₁ h₁ V T hT n) ha).trans
      (component_tmul_symbol R S X₁ Y₁ f₁ h₁ V T hT s (aR a) (fun i => aR (t i)))
  have hmid : (s • DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) ((f₁.appLE V T hT) (aR a))
      (fun i => (f₁.appLE V T hT) (aR (t i))) : DeRhamPresentationTo.DeRhamPresentation.Form S Γ(Y₁.left, T) n) =
      s • DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) (aS ((f₂.appLE U W hW) a))
        (fun i => aS ((f₂.appLE U W hW) (t i))) :=
    congrArg (fun ω => s • ω) (congrArg₂ (DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T))
      (ConcreteCategory.congr_hom hs a) (funext (fun i => ConcreteCategory.congr_hom hs (t i))))
  have hR : gS (component R S X₂ Y₂ f₂ h₂ U W hW n (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t)) =
      s • DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) (aS ((f₂.appLE U W hW) a))
        (fun i => aS ((f₂.appLE U W hW) (t i))) :=
    (congrArg gS (component_tmul_symbol R S X₂ Y₂ f₂ h₂ U W hW s a t)).trans
      ((gS.map_smul s _).trans (congrArg (fun ω => s • ω) hb))
  exact hL.trans (hmid.trans hR.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.FormsScalarOpenMap.BaseIntrinsicFormsScalarOpenMap
