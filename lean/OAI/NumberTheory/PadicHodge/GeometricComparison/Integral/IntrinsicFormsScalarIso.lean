import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeScalarForms

/-! # Intrinsic Forms Scalar Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicFormsScalarIso.IntegralIntrinsicFormsScalarIso

noncomputable section

/-! The original native form-presheaf scalar map is invertible on affine opens through degree two over arbitrary flat coefficient extensions. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

theorem component_isIso [Module.Flat R S]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) (hn : n ≤ 2) : IsIso (Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h U n) := by
  let : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.pushout R S X Y f U hp hU
  have he : Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.component R S X Y f h U n =
      (IntegralFirst.ThreeScalarForms.IntegralFirstThreeScalarForms.equiv R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n hn).toModuleIso.hom :=
    congrArg ModuleCat.ofHom (IntegralFirst.ThreeScalarForms.IntegralFirstThreeScalarForms.equiv_eq_map R S
      Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n hn).symm
  rw [he]
  exact (IntegralFirst.ThreeScalarForms.IntegralFirstThreeScalarForms.equiv R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n hn).toModuleIso.isIso_hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicFormsScalarIso.IntegralIntrinsicFormsScalarIso
