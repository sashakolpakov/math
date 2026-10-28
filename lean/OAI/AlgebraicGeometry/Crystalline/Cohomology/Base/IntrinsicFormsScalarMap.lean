import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.EtalePolynomialTower
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity

/-! # Intrinsic Forms Scalar Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap

noncomputable section

/-! The canonical scalar map on native form presheaves, natural for every restriction and invertible on affine opens with etale coordinates in a flat base-change square. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

def component (U : X.left.Opens) (n : ℕ) :
    (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).obj ((DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op U)) ⟶
      (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).obj (op (f ⁻¹ᵁ U)) := by
  letI : Algebra R Γ(X.left, U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  letI : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  letI : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  letI : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  letI : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceTower R S X Y f U h
  exact ModuleCat.ofHom (NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) n)

theorem naturality (n : ℕ) {U V : X.left.Opensᵒᵖ} (i : U ⟶ V) :
    (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).map ((DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map i) ≫
      component R S X Y f h V.unop n =
    component R S X Y f h U.unop n ≫
      (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).map ((Opens.map f.base).op.map i) := by
  let : Algebra R Γ(X.left, U.unop) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U.unop
  let : Algebra R Γ(X.left, V.unop) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X V.unop
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U.unop) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U.unop)
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ V.unop) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ V.unop)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.baseAlgebra R S X Y f U.unop
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ V.unop) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.baseAlgebra R S X Y f V.unop
  let : Algebra Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceAlgebra R S X Y f U.unop
  let : Algebra Γ(X.left, V.unop) Γ(Y.left, f ⁻¹ᵁ V.unop) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceAlgebra R S X Y f V.unop
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U.unop) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ V.unop) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceTower R S X Y f U.unop h
  let : IsScalarTower R Γ(X.left, V.unop) Γ(Y.left, f ⁻¹ᵁ V.unop) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceTower R S X Y f V.unop h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarNaturality.FormsBaseChange.formScalarMap_naturality R S
    Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) Γ(X.left, V.unop) Γ(Y.left, f ⁻¹ᵁ V.unop)
    ((AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i)
    ((AlgebraicForms.AlgebraicDeRham.sectionAlgebras S Y).map ((Opens.map f.base).op.map i))
    (fun a => ConcreteCategory.congr_hom (f.naturality i) a) n ω

def map (n : ℕ) : DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n ⋙ NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S ⟶
    (Opens.map f.base).op ⋙ DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n where
  app U := component R S X Y f h U.unop n
  naturality _ _ i := BaseIntrinsicFormsScalarMap.naturality R S X Y f h n i

variable (U : X.left.Opens) (σ : Type u) [LinearOrder σ]
local instance sourceCoefficients : Algebra R Γ(X.left, U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
variable [Algebra (MvPolynomial σ R) Γ(X.left, U)]
  [IsScalarTower R (MvPolynomial σ R) Γ(X.left, U)]
  [Algebra.Etale (MvPolynomial σ R) Γ(X.left, U)]

include σ in
theorem component_isIso [Module.Flat R S]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : IsAffineOpen U) (n : ℕ) : IsIso (component R S X Y f h U n) := by
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceTower R S X Y f U h
  let : Algebra.IsPushout R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.pushout R S X Y f U hp hU
  have he : component R S X Y f h U n =
      (EtalePolynomialTower.EtalePolynomialPushoutCoordinates.complexIso R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) σ).hom.f n :=
    (EtalePolynomialTower.EtalePolynomialPushoutCoordinates.component R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) σ n).symm
  rw [he]
  exact ((HomologicalComplex.eval (ModuleCat.{u} S) (.up ℕ) n).mapIso
    (EtalePolynomialTower.EtalePolynomialPushoutCoordinates.complexIso R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) σ)).isIso_hom

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap
