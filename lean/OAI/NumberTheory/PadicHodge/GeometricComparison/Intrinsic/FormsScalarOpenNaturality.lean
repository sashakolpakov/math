import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarHomExt

/-! # Forms Scalar Open Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarOpenNaturality.IntrinsicFormsScalarOpenMap

noncomputable section

/-! Scalar extension commutes with geometric pullback on all compatible open subsets of an actual commuting square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
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
    (FlatScalar.FlatScalarExtension.moduleFunctor R S).map (OpenSectionPullback.DeRham.formsPullbackLE u U V hu n) ≫
        FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component R S X₁ Y₁ f₁ h₁ V T hT n =
      FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component R S X₂ Y₂ f₂ h₂ U W hW n ≫ OpenSectionPullback.DeRham.formsPullbackLE v W T hv n := by
  let : Algebra R Γ(X₂.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X₂ U
  let : Algebra R Γ(X₁.left, V) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X₁ V
  let : Algebra S Γ(Y₂.left, W) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y₂ W
  let : Algebra S Γ(Y₁.left, T) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y₁ T
  let aR : CommAlgCat.of R Γ(X₂.left, U) ⟶ CommAlgCat.of R Γ(X₁.left, V) :=
    CommAlgCat.ofHom (OpenSectionPullback.DeRham.sectionPullbackLE u U V hu)
  let aS : CommAlgCat.of S Γ(Y₂.left, W) ⟶ CommAlgCat.of S Γ(Y₁.left, T) :=
    CommAlgCat.ofHom (OpenSectionPullback.DeRham.sectionPullbackLE v W T hv)
  let gS : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S Γ(Y₂.left, W) n →ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S Γ(Y₁.left, T) n := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap aS n
  have hs := Section.GeometricRestriction.SectionGeometricSquare.square u.left v.left f₁ f₂ hsquare U V W T hu hv hT hW
  apply Forms.ScalarHomExt.FormsHomExt.scalar_hom_ext R S Γ(X₂.left, U) n
  intro s a t
  have ha : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap aR n).baseChange S (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t) =
      s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₁.left, V) (aR a) (fun i => aR (t i)) :=
    (LinearMap.baseChange_tmul (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap aR n) s _).trans
      (congrArg (fun ω => s ⊗ₜ[R] ω) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol aR n a t))
  change FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component R S X₁ Y₁ f₁ h₁ V T hT n
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap aR n).baseChange S (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t)) =
    gS (FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component R S X₂ Y₂ f₂ h₂ U W hW n (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t))
  have hb : gS (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₂.left, W) ((f₂.appLE U W hW) a)
      (fun i => (f₂.appLE U W hW) (t i))) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) (aS ((f₂.appLE U W hW) a))
        (fun i => aS ((f₂.appLE U W hW) (t i))) := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol aS n _ _
  have hL : FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component R S X₁ Y₁ f₁ h₁ V T hT n
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap aR n).baseChange S (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t)) =
      s • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) ((f₁.appLE V T hT) (aR a))
        (fun i => (f₁.appLE V T hT) (aR (t i))) :=
    (congrArg (FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component R S X₁ Y₁ f₁ h₁ V T hT n) ha).trans
      (FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component_tmul_symbol R S X₁ Y₁ f₁ h₁ V T hT s (aR a) (fun i => aR (t i)))
  have hmid : (s • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) ((f₁.appLE V T hT) (aR a))
      (fun i => (f₁.appLE V T hT) (aR (t i))) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S Γ(Y₁.left, T) n) =
      s • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) (aS ((f₂.appLE U W hW) a))
        (fun i => aS ((f₂.appLE U W hW) (t i))) :=
    congrArg (fun ω => s • ω) (congrArg₂ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T))
      (ConcreteCategory.congr_hom hs a) (funext (fun i => ConcreteCategory.congr_hom hs (t i))))
  have hR : gS (FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component R S X₂ Y₂ f₂ h₂ U W hW n (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R Γ(X₂.left, U) a t)) =
      s • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(Y₁.left, T) (aS ((f₂.appLE U W hW) a))
        (fun i => aS ((f₂.appLE U W hW) (t i))) :=
    (congrArg gS (FormsScalarOpenMap.IntrinsicFormsScalarOpenMap.component_tmul_symbol R S X₂ Y₂ f₂ h₂ U W hW s a t)).trans
      ((gS.map_smul s _).trans (congrArg (fun ω => s • ω) hb))
  exact hL.trans (hmid.trans hR.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarOpenNaturality.IntrinsicFormsScalarOpenMap
