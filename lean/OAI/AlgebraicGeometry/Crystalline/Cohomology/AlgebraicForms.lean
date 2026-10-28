import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Algebraic Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

noncomputable section

/-!
# Cohomology: algebraic forms and their restriction maps

The degree-one objects are actual Kähler differentials. Pullback is induced
by their universal derivation. In particular these objects are independent
of crystalline cohomology and of the desired comparison theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R]

/-- Kähler one-forms, with the coefficient ring's module structure. -/
abbrev OneForms (A : CommAlgCat.{u} R) := KaehlerDifferential R A

variable {R}

/-- The pullback of Kähler differentials along an algebra homomorphism. -/
def oneFormsMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    OneForms R A →ₗ[R] OneForms R B := by
  letI : Algebra A B := f.hom.toRingHom.toAlgebra
  exact (KaehlerDifferential.map R R A B).restrictScalars R

@[simp]
theorem oneFormsMap_D {A B : CommAlgCat.{u} R} (f : A ⟶ B) (a : A) :
    oneFormsMap f (KaehlerDifferential.D R A a) = KaehlerDifferential.D R B (f a) := by
  let : Algebra A B := f.hom.toRingHom.toAlgebra
  exact KaehlerDifferential.map_D R R A B a

/-- Pullback has the correct semilinearity for the varying section ring. -/
theorem oneFormsMap_smul {A B : CommAlgCat.{u} R} (f : A ⟶ B) (a : A)
    (x : OneForms R A) : oneFormsMap f (a • x) = (f a) • oneFormsMap f x := by
  let : Algebra A B := f.hom.toRingHom.toAlgebra
  change KaehlerDifferential.map R R A B (a • x) =
    (algebraMap A B a) • KaehlerDifferential.map R R A B x
  rw [map_smul, algebraMap_smul]

@[simp]
theorem oneFormsMap_id (A : CommAlgCat.{u} R) (x : OneForms R A) :
    oneFormsMap (𝟙 A) x = x := by
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; simp
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | smul a x hx ih => rw [oneFormsMap_smul, ih]; rfl

theorem oneFormsMap_comp {A B C : CommAlgCat.{u} R} (f : A ⟶ B) (g : B ⟶ C)
    (x : OneForms R A) : oneFormsMap (f ≫ g) x = oneFormsMap g (oneFormsMap f x) := by
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; simp
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul a x hx ih => simp only [oneFormsMap_smul, CommAlgCat.comp_apply, ih]

/-- Kähler differentials as a functor of the coordinate algebra. -/
def oneFormsFunctor : CommAlgCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (OneForms R A)
  map f := ModuleCat.ofHom (oneFormsMap f)
  map_id A := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (oneFormsMap_id A)
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (oneFormsMap_comp f g)

/-- Algebraic `n`-forms are the exterior powers over the coordinate algebra. -/
abbrev Forms (A : CommAlgCat.{u} R) (n : ℕ) :=
  ⋀[A]^n (OneForms R A)

/-- Restrict the scalar ring of an alternating map. -/
def restrictAlternating {S : Type*} [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    {ι : Type*} (f : AlternatingMap S M N ι) : AlternatingMap R M N ι :=
  { f.toMultilinearMap.restrictScalars R with
    map_eq_zero_of_eq' := fun v _ _ hij hne => f.map_eq_zero_of_eq v hij hne }

/-- Pullback of arbitrary exterior powers of Kähler differentials. -/
def formsMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ) :
    Forms A n →ₗ[R] Forms B n := by
  letI : Algebra A B := f.hom.toRingHom.toAlgebra
  exact (exteriorPower.alternatingMapLinearEquiv
    ((restrictAlternating (R := A) (exteriorPower.ιMulti B n)).compLinearMap
      (KaehlerDifferential.map R R A B))).restrictScalars R

@[simp]
theorem formsMap_mk {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ)
    (v : Fin n → OneForms R A) :
    formsMap f n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => oneFormsMap f (v i)) := by
  let : Algebra A B := f.hom.toRingHom.toAlgebra
  change (exteriorPower.alternatingMapLinearEquiv
    ((restrictAlternating (R := A) (exteriorPower.ιMulti B n)).compLinearMap
      (KaehlerDifferential.map R R A B))) (exteriorPower.ιMulti A n v) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem formsMap_smul {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ)
    (a : A) (v : Forms A n) :
    formsMap f n (a • v) = (f a) • formsMap f n v := by
  let : Algebra A B := f.hom.toRingHom.toAlgebra
  change (exteriorPower.alternatingMapLinearEquiv _ : Forms A n →ₗ[A] Forms B n)
      (a • v) = (algebraMap A B a) • _
  rw [map_smul, algebraMap_smul]
  rfl

@[simp]
theorem formsMap_id (A : CommAlgCat.{u} R) (n : ℕ) (x : Forms A n) :
    formsMap (𝟙 A) n x = x := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; simp
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | smul a x hx ih => rw [formsMap_smul, ih]; rfl

theorem formsMap_comp {A B C : CommAlgCat.{u} R} (f : A ⟶ B) (g : B ⟶ C)
    (n : ℕ) (x : Forms A n) :
    formsMap (f ≫ g) n x = formsMap g n (formsMap f n x) := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; simp [oneFormsMap_comp]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul a x hx ih => simp only [formsMap_smul, CommAlgCat.comp_apply, ih]

/-- Algebraic forms in a fixed degree, functorial in the coordinate algebra. -/
def formsFunctor (n : ℕ) : CommAlgCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (Forms A n)
  map f := ModuleCat.ofHom (formsMap f n)
  map_id A := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (formsMap_id A n)
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (formsMap_comp f g n)

variable (R) (X : Over (Spec (CommRingCat.of R)))

/-- Constants in the section ring of an open subscheme. -/
def sectionBaseMap (U : X.left.Opens) : R →+* Γ(X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    X.hom.appLE ⊤ U (by simp)).hom

instance sectionAlgebra (U : X.left.Opens) : Algebra R Γ(X.left, U) :=
  (sectionBaseMap R X U).toAlgebra

theorem sectionBaseMap_naturality {U V : X.left.Opens} (f : op U ⟶ op V) (r : R) :
    X.left.presheaf.map f (sectionBaseMap R X U r) = sectionBaseMap R X V r := by
  have h := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g)
    (X.hom.appLE_map (U := ⊤) (V := U) (by simp) f)
  exact ConcreteCategory.congr_hom h r

/-- The actual structure presheaf, retaining the base-algebra action. -/
def sectionAlgebras : X.left.Opensᵒᵖ ⥤ CommAlgCat.{u} R where
  obj U := CommAlgCat.of R Γ(X.left, U.unop)
  map f := CommAlgCat.ofHom
    { (X.left.presheaf.map f).hom with
      commutes' := sectionBaseMap_naturality R X f }
  map_id U := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ConcreteCategory.congr_hom (X.left.presheaf.map_id U) x
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ConcreteCategory.congr_hom (X.left.presheaf.map_comp f g) x

/-- The Kähler differential presheaf on the scheme. -/
def oneFormsPresheaf : X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  sectionAlgebras R X ⋙ oneFormsFunctor

/-- The presheaf of exterior powers of Kähler differentials. -/
def formsPresheaf (n : ℕ) : X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  sectionAlgebras R X ⋙ formsFunctor n

/-- The sheaf of algebraic differential forms in degree `n`. -/
def formsSheaf (n : ℕ) : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R) :=
  (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).obj
    (formsPresheaf R X n)

/-- Functions as modules over the base. -/
def functionsPresheaf : X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  sectionAlgebras R X ⋙ forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙
    forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)

/-- The first de Rham differential is the universal derivation on sections. -/
def dZero : functionsPresheaf R X ⟶ oneFormsPresheaf R X where
  app U := ModuleCat.ofHom (KaehlerDifferential.D R Γ(X.left, U.unop)).toLinearMap
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (oneFormsMap_D ((sectionAlgebras R X).map f) a).symm

/-- The first de Rham differential on the associated sheaves. -/
def dZeroSheaf :
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).obj
      (functionsPresheaf R X) ⟶
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).obj
      (oneFormsPresheaf R X) :=
  (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).map (dZero R X)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham
