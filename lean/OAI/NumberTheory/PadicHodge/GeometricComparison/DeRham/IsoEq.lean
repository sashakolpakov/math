import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import Mathlib

/-! # Iso Eq -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoEq

noncomputable section

section

/-! Pullback by a scheme isomorphism is invertible on the actual form presheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))}
  (f : X ⟶ Y) [IsIso f]

instance sectionPullback_isIso (U : Y.left.Opens) :
    IsIso (CommAlgCat.ofHom (Int.sectionPullback f U)) := by
  let : IsIso f.left := inferInstanceAs (IsIso ((Over.forget _).map f))
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (f.left.app U)

instance formsPullback_isIso (n : ℕ) : IsIso (Int.formsPullback f n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  exact inferInstanceAs
    (IsIso ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsFunctor n).map (CommAlgCat.ofHom (Int.sectionPullback f U.unop))))

end

section

/-! Exact equivalences of the native Zariski sheaf categories under scheme isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))}
  (f : X ⟶ Y) [IsIso f]

def opensEquivalence : Y.left.Opens ≌ X.left.Opens :=
  Opens.mapMapIso (((Over.forget _).comp Scheme.forgetToTop).mapIso (asIso f))

theorem opensEquivalence_functor : (opensEquivalence f).functor = Opens.map f.left.base := rfl

theorem opensEquivalence_inverse :
    (opensEquivalence f).inverse = Opens.map (inv f).left.base := rfl

instance opensMap_cocontinuous : (Opens.map f.left.base).IsCocontinuous
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left) := by
  exact ((opensEquivalence f).toAdjunction.isCocontinuous_iff_coverPreserving
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)).mpr
      (coverPreserving_opens_map (inv f).left.base)

instance opensMap_dense : (Opens.map f.left.base).IsDenseSubsite
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left) := by
  let e := opensEquivalence f
  let : e.functor.IsCocontinuous (Opens.grothendieckTopology Y.left)
      (Opens.grothendieckTopology X.left) := opensMap_cocontinuous f
  let : e.inverse.IsCocontinuous (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology Y.left) := opensMap_cocontinuous (inv f)
  exact e.isDenseSubsite_functor_of_isCocontinuous _ _

instance directImage_isEquivalence : (Int.directImage f).IsEquivalence :=
  inferInstanceAs ((Opens.map f.left.base).sheafPushforwardContinuous (ModuleCat R)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)).IsEquivalence

end

/-! The native sheaf-complex pullback along a scheme isomorphism is an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))}
  (f : X ⟶ Y) [IsIso f]

instance inverseImage_isEquivalence : (Int.inverseImage f).IsEquivalence :=
  (Int.imageAdjunction f).isEquivalence_left_of_isEquivalence_right

instance presheafPullback_isIso : IsIso (Int.presheafPullback f) := by
  let : ∀ n : ℕ, IsIso ((Int.presheafPullback f).f n) := fun n => formsPullback_isIso f n
  exact HomologicalComplex.Hom.isIso_of_components _

def directImageSheafificationIso :
    ((presheafToSheaf (Opens.grothendieckTopology Y.left) (ModuleCat R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (((Int.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) ≅
      ((Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
  (NatIso.mapHomologicalComplex
    ((Opens.map f.left.base).pushforwardContinuousSheafificationCompatibility (ModuleCat R)
      (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left))
    (ComplexShape.up ℕ)).app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

theorem directImageSheafificationIso_unit :
    (Int.sheafificationComplexAdjunction Y).unit.app
        (((Int.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) ≫
      ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat R)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (directImageSheafificationIso f).hom =
      ((Int.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((Int.sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (Opens.map f.left.base).toSheafify_pullbackSheafificationCompatibility (ModuleCat R)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)

theorem sheafDirectImage_eq_iso : Int.sheafDirectImage f =
    ((presheafToSheaf (Opens.grothendieckTopology Y.left) (ModuleCat R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Int.presheafPullback f) ≫ (directImageSheafificationIso f).hom := by
  let adj := Int.sheafificationComplexAdjunction Y
  let U := (sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let D := (Int.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)
  apply (adj.homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y)
    (((Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))).injective
  rw [show (adj.homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y)
      (((Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)))
        (Int.sheafDirectImage f) = Int.presheafToDirectImageSheafComplex f from
    (adj.homEquiv _ _).apply_symm_apply (Int.presheafToDirectImageSheafComplex f),
    Adjunction.homEquiv_unit]
  change Int.presheafToDirectImageSheafComplex f =
    adj.unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y) ≫
      U.map (_ ≫ (directImageSheafificationIso f).hom)
  rw [U.map_comp, ← Category.assoc]
  have hn := adj.unit.naturality (Int.presheafPullback f)
  change Int.presheafPullback f ≫ adj.unit.app (D.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) =
    adj.unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y) ≫ U.map _ at hn
  rw [← hn, Category.assoc, directImageSheafificationIso_unit]
  rfl

instance sheafDirectImage_isIso : IsIso (Int.sheafDirectImage f) := by
  rw [sheafDirectImage_eq_iso]
  exact (((presheafToSheaf (Opens.grothendieckTopology Y.left) (ModuleCat R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).mapIso (asIso (Int.presheafPullback f)) ≪≫
      directImageSheafificationIso f).isIso_hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoEq
