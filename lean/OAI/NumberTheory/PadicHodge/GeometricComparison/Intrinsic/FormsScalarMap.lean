import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.AffineFormVanishing

/-! # Forms Scalar Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap

noncomputable section

/-! The canonical scalar map on native form presheaves, natural for every restriction and invertible on affine opens in a flat base-change square. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

def component (U : X.left.Opens) (n : ℕ) :
    (FlatScalar.FlatScalarExtension.moduleFunctor R S).obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U)) ⟶
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).obj (op (f ⁻¹ᵁ U)) := by
  letI : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  letI : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  letI : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  letI : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  letI : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  exact ModuleCat.ofHom (Forms.ScalarMap.FormsBaseChange.formScalarMap R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n)

theorem naturality (n : ℕ) {U V : X.left.Opensᵒᵖ} (i : U ⟶ V) :
    (FlatScalar.FlatScalarExtension.moduleFunctor R S).map ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map i) ≫
      component R S X Y f h V.unop n =
    component R S X Y f h U.unop n ≫
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).map ((Opens.map f.base).op.map i) := by
  let : Algebra R Γ(X.left, U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U.unop
  let : Algebra R Γ(X.left, V.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X V.unop
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U.unop)
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ V.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ V.unop)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U.unop
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ V.unop) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f V.unop
  let : Algebra Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U.unop
  let : Algebra Γ(X.left, V.unop) Γ(Y.left, f ⁻¹ᵁ V.unop) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f V.unop
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U.unop) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ V.unop) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U.unop h
  let : IsScalarTower R Γ(X.left, V.unop) Γ(Y.left, f ⁻¹ᵁ V.unop) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f V.unop h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact Forms.ScalarNaturality.FormsBaseChange.formScalarMap_naturality R S
    Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) Γ(X.left, V.unop) Γ(Y.left, f ⁻¹ᵁ V.unop)
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i)
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras S Y).map ((Opens.map f.base).op.map i))
    (fun a => ConcreteCategory.congr_hom (f.naturality i) a) n ω

def map (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n ⋙ FlatScalar.FlatScalarExtension.moduleFunctor R S ⟶
    (Opens.map f.base).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n where
  app U := component R S X Y f h U.unop n
  naturality _ _ i := IntrinsicFormsScalarMap.naturality R S X Y f h n i

theorem component_isIso [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) : IsIso (component R S X Y f h U n) := by
  let : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.pushout R S X Y f U hp hU
  let : Algebra ℚ Γ(X.left, U) := Rational.AffineFormVanishing.RationalAffineFormVanishing.sectionAlgebra R X U
  let : Algebra ℚ Γ(Y.left, f ⁻¹ᵁ U) := Rational.AffineFormVanishing.RationalAffineFormVanishing.sectionAlgebra S Y (f ⁻¹ᵁ U)
  have he : component R S X Y f h U n =
      (Forms.ScalarEquivalence.FormsBaseChange.formsScalarEquiv R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n).toModuleIso.hom :=
    congrArg ModuleCat.ofHom (Forms.ScalarEquivalence.FormsBaseChange.formsScalarEquiv_eq_map R S
      Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n).symm
  rw [he]
  exact (Forms.ScalarEquivalence.FormsBaseChange.formsScalarEquiv R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n).toModuleIso.isIso_hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap
