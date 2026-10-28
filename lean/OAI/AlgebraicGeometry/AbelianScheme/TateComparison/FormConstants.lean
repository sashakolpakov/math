import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Neighbors
import OAI.AlgebraicGeometry.Betti.Scheme
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Form Constants -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants

noncomputable section

section

/-!
Algebraic one-forms are compatible Kahler differentials on affine test
schemes. This is the functor-of-points description of global sections of
the sheaf of relative differentials. Pullback is constructed by composing
the test-scheme maps. No trace map or Hecke formula is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- An affine complex test scheme with its specified structure morphism. -/
abbrev affineComplexTest (R : CommAlgCat.{0} ℂ) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))

/-- A homomorphism of complex algebras induces the actual affine scheme map. -/
def affineComplexMap {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    affineComplexTest S ⟶ affineComplexTest R :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun x => f.hom.commutes x))

/-- The actual induced map of Kahler differentials, restricted to complex scalars. -/
def differentialMap {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    KaehlerDifferential ℂ R →ₗ[ℂ] KaehlerDifferential ℂ S := by
  let : Algebra R S := f.hom.toAlgebra
  let : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq
    (fun x => (f.hom.commutes x).symm)
  exact (KaehlerDifferential.map ℂ ℂ R S).restrictScalars ℂ

/-- Compatible differentials on all affine tests, with their pointwise
complex vector-space structure. -/
def globalOneForms (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Submodule ℂ (∀ (R : CommAlgCat.{0} ℂ),
      (affineComplexTest R ⟶ X) → KaehlerDifferential ℂ R) where
  carrier := {ω | ∀ (R S : CommAlgCat.{0} ℂ) (f : R ⟶ S) (x : affineComplexTest R ⟶ X),
    differentialMap f (ω R x) = ω S (affineComplexMap f ≫ x)}
  zero_mem' R S f x := map_zero _
  add_mem' hω hη R S f x := by
    change differentialMap f (_ + _) = _ + _
    rw [map_add, hω R S f x, hη R S f x]
  smul_mem' c ω hω R S f x := by
    change differentialMap f (c • _) = c • _
    rw [map_smul, hω R S f x]

abbrev OneForms (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) := globalOneForms X

/-- Pullback of one-forms along the actual algebraic scheme morphism. -/
def formsPullback {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    OneForms Y →ₗ[ℂ] OneForms X where
  toFun ω := ⟨fun R x => ω.val R (x ≫ f), by
    intro R S g x
    exact (ω.property R S g (x ≫ f)).trans
      (congrArg (ω.val S) (Category.assoc _ _ _).symm)⟩
  map_add' ω η := rfl
  map_smul' c ω := rfl

@[simp]
theorem formsPullback_id (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    formsPullback (𝟙 X) = LinearMap.id := by
  apply LinearMap.ext
  intro ω
  apply Subtype.ext
  funext R x
  exact congrArg (ω.val R) (Category.comp_id x)

theorem formsPullback_comp {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    formsPullback (f ≫ g) = (formsPullback f).comp (formsPullback g) := by
  apply LinearMap.ext
  intro ω
  apply Subtype.ext
  funext R x
  exact congrArg (ω.val R) (Category.assoc x f g).symm

end

/-! Actual affine-test one-forms vanish on constant maps. This removes
the base-point normalization term in Albanese pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def scalarAffineTestIso : affineComplexTest (CommAlgCat.of ℂ ℂ) ≅ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) :=
  Over.isoMk (Iso.refl _) (by simp [affineComplexTest])

def scalarTestAlgebraMap (R : CommAlgCat.{0} ℂ) : CommAlgCat.of ℂ ℂ ⟶ R :=
  CommAlgCat.ofHom (Algebra.ofId ℂ R)

theorem forms_at_constant {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (ω : OneForms X)
    (p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X) (R : CommAlgCat.{0} ℂ)
    (a : affineComplexTest R ⟶ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) : ω.val R (a ≫ p) = 0 := by
  have : Subsingleton (KaehlerDifferential ℂ ℂ) :=
    KaehlerDifferential.subsingleton_of_surjective ℂ ℂ (fun z => ⟨z, rfl⟩)
  have hz : ω.val (CommAlgCat.of ℂ ℂ) (scalarAffineTestIso.hom ≫ p) = 0 := Subsingleton.elim _ _
  have h := ω.property (CommAlgCat.of ℂ ℂ) R (scalarTestAlgebraMap R) (scalarAffineTestIso.hom ≫ p)
  rw [hz, map_zero] at h
  have ha : affineComplexMap (scalarTestAlgebraMap R) ≫ scalarAffineTestIso.hom = a :=
    Over.mkIdTerminal.hom_ext _ _
  have hp : affineComplexMap (scalarTestAlgebraMap R) ≫ scalarAffineTestIso.hom ≫ p = a ≫ p :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) ha)
  exact (congrArg (ω.val R) hp).symm.trans h.symm

theorem formsPullback_constant {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ Y) (a : X ⟶ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) :
    formsPullback (a ≫ p) = 0 := by
  apply LinearMap.ext
  intro ω
  apply Subtype.ext
  funext R x
  change ω.val R (x ≫ a ≫ p) = 0
  rw [← Category.assoc]
  exact forms_at_constant ω p R (x ≫ a)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants
