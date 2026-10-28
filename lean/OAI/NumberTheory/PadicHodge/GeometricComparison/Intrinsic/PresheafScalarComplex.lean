import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsScalarMap

/-! # Presheaf Scalar Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex

noncomputable section

/-! The canonical scalar map commutes with the native de Rham differential before sheafification. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
open OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

def scalar : (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} R) ⥤ (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} S) :=
  (Functor.whiskeringRight _ _ _).obj (FlatScalar.FlatScalarExtension.moduleFunctor R S)

def preimage : (Y.left.Opensᵒᵖ ⥤ ModuleCat.{0} S) ⥤ (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} S) :=
  (Functor.whiskeringLeft _ _ _).obj (Opens.map f.base).op

instance scalar_additive : (scalar R S X).Additive := by
  dsimp [scalar]
  infer_instance

instance preimage_additive : (preimage R S X Y f).Additive := by
  dsimp [preimage]
  infer_instance

theorem differential (n : ℕ) :
    (scalar R S X).map (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X n) ≫
      FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f h (n + 1) =
    FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f h n ≫
      (preimage R S X Y f).map (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf S Y n) := by
  apply NatTrans.ext
  funext U
  let : Algebra R Γ(X.left, U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U.unop
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U.unop)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U.unop
  let : Algebra Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U.unop
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U.unop) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U.unop h
  apply ModuleCat.hom_ext
  exact LinearMap.ext (Forms.ScalarMap.FormsBaseChange.formScalarMap_differential R S
    Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) n)

def map : ((scalar R S X).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) ⟶
    ((preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y) where
  f n := FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f h n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    change FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f h n ≫
        (preimage R S X Y f).map ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y).d n (n + 1)) =
      (scalar R S X).map ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d n (n + 1)) ≫
        FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f h (n + 1)
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y).d n (n + 1) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf S Y n from CochainComplex.of_d _ _ n]
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d n (n + 1) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X n from CochainComplex.of_d _ _ n]
    exact (differential R S X Y f h n).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex
