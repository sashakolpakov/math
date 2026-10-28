import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeReduction

/-! # Reduction Presheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionPresheaf.IntrinsicIntegralReductionPresheaf

noncomputable section

/-! The actual coefficient-reduction map on native form presheaves, with exact affine kernels in the first two degrees. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

def target (n : ℕ) : X.left.Opensᵒᵖ ⥤ ModuleCat R :=
  (Opens.map f.base).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n ⋙
    ModuleCat.restrictScalars (algebraMap R S)

def component (U : X.left.Opens) (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U) ⟶ (target R S X Y f n).obj (op U) := by
  let : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  change ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R Γ(X.left, U) n) ⟶
    ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S Γ(Y.left, f ⁻¹ᵁ U) n)
  exact ModuleCat.ofHom (Forms.ScalarMap.FormsBaseChange.formExtensionMap R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n)

theorem component_eq_one_tmul (U : X.left.Opens) (n : ℕ)
    (ω : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U)) :
    component R S X Y f h U n ω = Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h U n (1 ⊗ₜ[R] ω) := by
  let : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  change Forms.ScalarMap.FormsBaseChange.formExtensionMap R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n ω =
    (1 : S) • Forms.ScalarMap.FormsBaseChange.formExtensionMap R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n ω
  exact (one_smul S _).symm

theorem naturality (n : ℕ) {U V : X.left.Opensᵒᵖ} (i : U ⟶ V) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map i ≫ component R S X Y f h V.unop n =
      component R S X Y f h U.unop n ≫ (target R S X Y f n).map i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  have hh := ConcreteCategory.congr_hom (Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.naturality R S X Y f h n i)
    (1 ⊗ₜ[R] ω)
  change Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h V.unop n
      (((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map i).hom.baseChange S (1 ⊗ₜ[R] ω)) = _ at hh
  rw [LinearMap.baseChange_tmul] at hh
  change component R S X Y f h V.unop n ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map i ω) =
    (target R S X Y f n).map i (component R S X Y f h U.unop n ω)
  rw [component_eq_one_tmul, component_eq_one_tmul]
  exact hh

def map (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n ⟶ target R S X Y f n where
  app U := component R S X Y f h U.unop n
  naturality _ _ i := IntrinsicIntegralReductionPresheaf.naturality R S X Y f h n i

theorem affine_surjective
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) (hn : n ≤ 1)
    (hS : Function.Surjective (algebraMap R S)) :
    Function.Surjective (component R S X Y f h U n) := by
  let : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.pushout R S X Y f U hp hU
  have he : (component R S X Y f h U n).hom =
      Forms.ScalarMap.FormsBaseChange.formExtensionMap R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n := by
    rfl
  change Function.Surjective (component R S X Y f h U n).hom
  rw [he]
  exact Integral.LowDegreeReduction.IntegralLowDegreeReduction.surjective R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n hn hS

theorem affine_zero_iff_divisible
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) (hn : n ≤ 1)
    (hS : Function.Surjective (algebraMap R S)) (r : R)
    (hr : RingHom.ker (algebraMap R S) = Ideal.span {r})
    (ω : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U)) :
    component R S X Y f h U n ω = 0 ↔
      ∃ η : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U), r • η = ω := by
  let iRA : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let iSB : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let iRB : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let iAB : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let iRSB : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let iRAB : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  let iPush : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.pushout R S X Y f U hp hU
  have hh := @Integral.LowDegreeReduction.IntegralLowDegreeReduction.zero_iff_divisible R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U)
    _ _ _ _ _ iRA iRB iAB iSB iRAB iRSB iPush n hn hS r hr ω
  exact hh

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionPresheaf.IntrinsicIntegralReductionPresheaf
