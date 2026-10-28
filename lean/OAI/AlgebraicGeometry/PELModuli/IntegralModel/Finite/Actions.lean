import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Actions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions

noncomputable section

/-!
Finite multiplication-table equations for integral actions. The action on
the whole ring of integers is constructed from finitely many actual group
endomorphisms, rather than supplied as an extra moduli parameter.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Module
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

section Rings

variable {R : Type u} [Ring R] {V : Type v} [Ring V]
  {Idx : Type*} (b : Basis Idx ℤ R) (v : Idx → V)

/-- The additive extension of the finitely specified values. -/
def basisExtension : R →ₗ[ℤ] V := b.constr ℤ v

@[simp] theorem basisExtension_basis (i : Idx) : basisExtension b v (b i) = v i :=
  b.constr_basis ℤ v i

/-- Multiplicativity on a basis implies multiplicativity everywhere. -/
theorem basisExtension_mul
    (hmul : ∀ i j, basisExtension b v (b i * b j) = v i * v j) (x y : R) :
    basisExtension b v (x * y) = basisExtension b v x * basisExtension b v y := by
  let L := basisExtension b v
  let lhs : R →ₗ[ℤ] R →ₗ[ℤ] V := (LinearMap.mul ℤ R).compr₂ L
  let rhs : R →ₗ[ℤ] R →ₗ[ℤ] V := (LinearMap.mul ℤ V).compl₁₂ L L
  have h : lhs = rhs := b.ext fun i => b.ext fun j => by
    change L (b i * b j) = L (b i) * L (b j)
    exact (hmul i j).trans (by simp [L])
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- A finite multiplication table and the unit equation construct the
unique ring homomorphism with the prescribed basis values. -/
def ringHomOfBasis
    (hone : basisExtension b v 1 = 1)
    (hmul : ∀ i j, basisExtension b v (b i * b j) = v i * v j) : R →+* V where
  toFun := basisExtension b v
  map_zero' := map_zero _
  map_one' := hone
  map_add' := map_add _
  map_mul' := basisExtension_mul b v hmul

@[simp] theorem ringHomOfBasis_basis
    (hone : basisExtension b v 1 = 1)
    (hmul : ∀ i j, basisExtension b v (b i * b j) = v i * v j) (i : Idx) :
    ringHomOfBasis b v hone hmul (b i) = v i := basisExtension_basis b v i

theorem ringHomOfBasis_unique
    (hone : basisExtension b v 1 = 1)
    (hmul : ∀ i j, basisExtension b v (b i * b j) = v i * v j)
    (ρ : R →+* V) (hρ : ∀ i, ρ (b i) = v i) :
    ρ = ringHomOfBasis b v hone hmul := by
  let L : R →ₗ[ℤ] V := ρ.toAddMonoidHom.toIntLinearMap
  have h : L = basisExtension b v := b.ext fun i => (hρ i).trans
    (basisExtension_basis b v i).symm
  exact RingHom.ext fun x => LinearMap.congr_fun h x

end Rings

variable {g : ℕ} {S : Scheme.{u}} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

/-- The ordinary endomorphism ring of the actual commutative group scheme.
Its multiplication is composition in the order used by IntegralAction. -/
def GroupEndRing := Additive (Grp.mk A.scheme ⟶ Grp.mk A.scheme)

instance : AddCommGroup (GroupEndRing A) :=
  inferInstanceAs (AddCommGroup (Additive (Grp.mk A.scheme ⟶ Grp.mk A.scheme)))

instance : Ring (GroupEndRing A) where
  one := Additive.ofMul (𝟙 _)
  mul f g := Additive.ofMul (g.toMul ≫ f.toMul)
  mul_assoc f g h := congrArg Additive.ofMul (Category.assoc h.toMul g.toMul f.toMul).symm
  one_mul f := congrArg Additive.ofMul (Category.comp_id f.toMul)
  mul_one f := congrArg Additive.ofMul (Category.id_comp f.toMul)
  left_distrib f g h := congrArg Additive.ofMul (MonObj.mul_comp g.toMul h.toMul f.toMul)
  right_distrib f g h := congrArg Additive.ofMul (MonObj.comp_mul h.toMul f.toMul g.toMul)
  zero_mul f := congrArg Additive.ofMul (MonObj.comp_one f.toMul)
  mul_zero f := congrArg Additive.ofMul (MonObj.one_comp f.toMul)

def GroupEndRing.hom (f : GroupEndRing A) : A.scheme ⟶ A.scheme := f.toMul.hom.hom

instance (f : GroupEndRing A) : IsMonHom (f.hom A) := f.toMul.hom.isMonHom_hom

def GroupEndRing.ofHom (f : A.scheme ⟶ A.scheme) [IsMonHom f] : GroupEndRing A :=
  Additive.ofMul (Grp.homMk f)

@[simp] theorem GroupEndRing.hom_ofHom (f : A.scheme ⟶ A.scheme) [IsMonHom f] :
    (GroupEndRing.ofHom A f).hom A = f := rfl

@[ext] theorem GroupEndRing.ext {f h : GroupEndRing A}
    (heq : f.hom A = h.hom A) : f = h := by
  apply Additive.toMul.injective
  exact Grp.hom_ext _ _ heq

@[simp] theorem GroupEndRing.hom_zero : (0 : GroupEndRing A).hom A = 1 := rfl
@[simp] theorem GroupEndRing.hom_one : (1 : GroupEndRing A).hom A = 𝟙 A.scheme := rfl
@[simp] theorem GroupEndRing.hom_add (f h : GroupEndRing A) :
    (f + h).hom A = f.hom A * h.hom A := rfl
@[simp] theorem GroupEndRing.hom_mul (f h : GroupEndRing A) :
    (f * h).hom A = h.hom A ≫ f.hom A := rfl

/-- Convert the ordinary endomorphism-ring map into the exact geometric
IntegralAction used by the PEL functor. -/
def integralActionOfRingHom {R : Type v} [CommRing R] (ρ : R →+* GroupEndRing A) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A where
  map x := (ρ x).hom A
  preservesGroup _ := inferInstance
  map_zero := by rw [ρ.map_zero, GroupEndRing.hom_zero]
  map_one := by rw [ρ.map_one, GroupEndRing.hom_one]
  map_add x y := by rw [ρ.map_add, GroupEndRing.hom_add]
  map_mul x y := by rw [ρ.map_mul, GroupEndRing.hom_mul]

def ringHomOfIntegralAction {R : Type v} [CommRing R] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) :
    R →+* GroupEndRing A where
  toFun x := GroupEndRing.ofHom A (ρ.map x)
  map_zero' := by apply GroupEndRing.ext; exact ρ.map_zero
  map_one' := by apply GroupEndRing.ext; exact ρ.map_one
  map_add' x y := by apply GroupEndRing.ext; exact ρ.map_add x y
  map_mul' x y := by apply GroupEndRing.ext; exact ρ.map_mul x y

theorem integralAction_ext {R : Type v} [CommRing R]
    {ρ σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A} (h : ∀ x, ρ.map x = σ.map x) : ρ = σ := by
  cases ρ
  cases σ
  congr
  exact funext h

/-- Action intertwiners are determined by the same finite integral basis. -/
theorem action_intertwines_iff_basis
    {R : Type v} [CommRing R] {Idx : Type*} (b : Basis Idx ℤ R)
    {h : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    (∀ x, ρ.map x ≫ f = f ≫ σ.map x) ↔
      ∀ i, ρ.map (b i) ≫ f = f ≫ σ.map (b i) := by
  constructor
  · exact fun h i => h (b i)
  · intro hb
    let L : R →+ Additive (A.scheme ⟶ B.scheme) :=
      { toFun := fun x => Additive.ofMul (ρ.map x ≫ f)
        map_zero' := congrArg Additive.ofMul
          ((congrArg (fun k => k ≫ f) ρ.map_zero).trans (MonObj.one_comp f))
        map_add' x y := congrArg Additive.ofMul
          ((congrArg (fun k => k ≫ f) (ρ.map_add x y)).trans
            (MonObj.mul_comp _ _ f)) }
    let R' : R →+ Additive (A.scheme ⟶ B.scheme) :=
      { toFun := fun x => Additive.ofMul (f ≫ σ.map x)
        map_zero' := congrArg Additive.ofMul
          ((congrArg (fun k => f ≫ k) σ.map_zero).trans (MonObj.comp_one f))
        map_add' x y := congrArg Additive.ofMul
          ((congrArg (fun k => f ≫ k) (σ.map_add x y)).trans
            (MonObj.comp_mul f _ _)) }
    have heq : L.toIntLinearMap = R'.toIntLinearMap := b.ext fun i =>
      congrArg Additive.ofMul (hb i)
    intro x
    exact congrArg Additive.toMul (LinearMap.congr_fun heq x)

variable {T : Scheme.{u}}

/-- Actual pullback of the endomorphism ring. -/
def GroupEndRing.pullback (f : T ⟶ S) : GroupEndRing A →+* GroupEndRing (A.pullback f) where
  toFun e := by
    have : IsMonHom (e.hom A) := inferInstance
    have hp : IsMonHom ((Over.pullback f).map (e.hom A)) := inferInstance
    exact @GroupEndRing.ofHom g T (A.pullback f) ((Over.pullback f).map (e.hom A)) hp
  map_zero' := by
    apply GroupEndRing.ext
    exact (Over.pullback f).map_one
  map_one' := by
    apply GroupEndRing.ext
    exact (Over.pullback f).map_id A.scheme
  map_add' e d := by
    apply GroupEndRing.ext
    exact (Over.pullback f).map_mul (e.hom A) (d.hom A)
  map_mul' e d := by
    apply GroupEndRing.ext
    exact (Over.pullback f).map_comp (d.hom A) (e.hom A)

theorem integralActionOfRingHom_pullback {R : Type v} [CommRing R]
    (ρ : R →+* GroupEndRing A) (f : T ⟶ S) :
    (integralActionOfRingHom A ρ).pullback f =
      integralActionOfRingHom (A.pullback f) ((GroupEndRing.pullback A f).comp ρ) := by
  apply integralAction_ext
  intro x
  rfl

variable (E : Type v) [Field E] [NumberField E]

abbrev integralActionBasis := Module.finBasis ℤ (NumberField.RingOfIntegers E)

/-- There are finitely many equations: one unit equation and one equation
for each pair of elements of a finite integral basis. -/
def IntegralActionTableEquations
    (f : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) → GroupEndRing A) : Prop :=
  basisExtension (integralActionBasis E) f 1 = 1 ∧
    ∀ i j, basisExtension (integralActionBasis E) f
      (integralActionBasis E i * integralActionBasis E j) = f i * f j

/-- Construct the unique integral action satisfying the given finite
multiplication table of actual group endomorphisms. -/
theorem integral_action_of_finite_table
    (f : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) → GroupEndRing A)
    (hf : IntegralActionTableEquations A E f) :
    ∃! ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A,
      ∀ i, ρ.map (integralActionBasis E i) = (f i).hom A := by
  let r := ringHomOfBasis (integralActionBasis E) f hf.1 hf.2
  refine ⟨integralActionOfRingHom A r, ?_, ?_⟩
  · intro i
    exact congrArg (GroupEndRing.hom A) (ringHomOfBasis_basis _ _ hf.1 hf.2 i)
  · intro ρ hρ
    have heq : ringHomOfIntegralAction A ρ = r := ringHomOfBasis_unique _ _ hf.1 hf.2
      (ringHomOfIntegralAction A ρ) (fun i => GroupEndRing.ext A (hρ i))
    apply integralAction_ext A
    intro x
    exact congrArg (GroupEndRing.hom A) (RingHom.congr_fun heq x)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions
