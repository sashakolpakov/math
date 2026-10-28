import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups

noncomputable section

/-!
Subgroups of the actual abelian point functor, including integral split
eigenblocks and isogeny kernels. Finite etale representability below means
representation by an actual finite etale subgroup scheme with a monomorphic
inclusion. It asserts neither a PEL quotient nor a Hecke correspondence.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ}

/-- A subgroup subfunctor of the actual functor of points of A. -/
structure PointSubgroup (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) where
  atTest : ∀ T : Over S, Subgroup (T ⟶ A.scheme)
  pullback_mem : ∀ {T U : Over S} (f : T ⟶ U) (x : U ⟶ A.scheme),
    x ∈ atTest U → f ≫ x ∈ atTest T

namespace PointSubgroup

variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

@[ext]
theorem ext {F G : PointSubgroup A} (h : ∀ T, F.atTest T = G.atTest T) : F = G := by
  cases F
  cases G
  congr
  exact funext h

/-- The kernel subfunctor of a genuine group morphism. -/
def kernel {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    PointSubgroup A where
  atTest T := (A.mapPoints B f T).ker
  pullback_mem h x hx := by
    change (h ≫ x) ≫ f = 1
    change x ≫ f = 1 at hx
    rw [Category.assoc, hx, MonObj.comp_one]

/-- Intersections retain their actual subgroup functor structure. -/
def inf (F G : PointSubgroup A) : PointSubgroup A where
  atTest T := F.atTest T ⊓ G.atTest T
  pullback_mem f x hx := ⟨F.pullback_mem f x hx.1, G.pullback_mem f x hx.2⟩

/-- Inverse image of a subgroup functor under an actual algebraic map. -/
def comapHom {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (F : PointSubgroup B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] : PointSubgroup A where
  atTest T := (F.atTest T).comap (A.mapPoints B f T)
  pullback_mem h x hx := by
    change (h ≫ x) ≫ f ∈ F.atTest _
    rw [Category.assoc]
    exact F.pullback_mem h (x ≫ f) hx

/-- Base change uses the proved group equivalence on actual test-scheme points. -/
def pullback {S' : Scheme.{u}} (F : PointSubgroup A) (f : S' ⟶ S) :
    PointSubgroup (A.pullback f) where
  atTest T := (F.atTest ((Over.map f).obj T)).comap
    (A.baseChangePointsMulEquiv f T).toMonoidHom
  pullback_mem {T U} h x hx := by
    change A.baseChangePointsMulEquiv f T (h ≫ x) ∈ F.atTest _
    have he : A.baseChangePointsMulEquiv f T (h ≫ x) =
        (Over.map f).map h ≫ A.baseChangePointsMulEquiv f U x := by
      apply Over.OverMorphism.ext
      exact Category.assoc _ _ _
    rw [he]
    exact F.pullback_mem ((Over.map f).map h) (A.baseChangePointsMulEquiv f U x) hx

/-- The standard meaning of a finite etale subgroup scheme. The point
subfunctor is the image of a monomorphic algebraic group-scheme inclusion. -/
def HasFiniteEtaleModel (F : PointSubgroup A) : Prop :=
  ∃ (H : CommGrp (Over S)) (i : H.X ⟶ A.scheme),
    IsMonHom i ∧ Mono i ∧ IsFinite H.X.hom ∧ Etale H.X.hom ∧
      ∀ (T : Over S) (x : T ⟶ A.scheme),
        x ∈ F.atTest T ↔ ∃ h : T ⟶ H.X, h ≫ i = x

/-- The geometric elementary-divisor type uses the genuine fiber subgroup. -/
def HasGeometricType (F : PointSubgroup A) (q : ℕ) (a : Fin 3 → ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
    Nonempty (F.atTest (Over.mk t) ≃* Multiplicative (∀ i : Fin 3, ZMod (q ^ a i)))

end PointSubgroup

variable {R : Type u} [CommRing R] {N q : ℕ} [Fact q.Prime]
  (A : PEL.PELFamilyData R g N S)

/-- The chosen split q^h-torsion block is an eigensubgroup of the actual
integral action. The local character determines scalars modulo q^h. -/
def splitBlock (χ : R →+* ℤ_[q]) (h : ℕ) : PointSubgroup A.abelian where
  atTest T := {
    carrier := {x | x ^ (q ^ h) = 1 ∧ ∀ b : R,
      x ≫ End.endSchemeMap A.abelian.scheme (A.action b) =
        x ^ (PadicInt.toZModPow h (χ b)).val}
    one_mem' := by
      refine ⟨one_pow _, ?_⟩
      intro b
      rw [MonObj.one_comp, one_pow]
    mul_mem' := by
      intro x y hx hy
      refine ⟨by rw [mul_pow, hx.1, hy.1, mul_one], ?_⟩
      intro b
      rw [MonObj.mul_comp, hx.2 b, hy.2 b, mul_pow]
    inv_mem' := by
      intro x hx
      refine ⟨by rw [inv_pow, hx.1, inv_one], ?_⟩
      intro b
      rw [GrpObj.inv_comp, hx.2 b, inv_pow] }
  pullback_mem f x hx := by
    refine ⟨?_, ?_⟩
    · rw [← MonObj.comp_pow, hx.1, MonObj.comp_one]
    · intro b
      rw [Category.assoc, hx.2 b, MonObj.comp_pow]

/-- Independent chosen-side finite etale subgroup choices. Their targets
and quotient polarizations are not part of this type. -/
def KernelChoices {s : ℕ} (χ : Fin s → R →+* ℤ_[q]) (h : ℕ)
    (a : Fin s → Fin 3 → ℕ) :=
  {F : Fin s → PointSubgroup A.abelian // ∀ v,
    (F v).HasFiniteEtaleModel ∧
      (∀ T, (F v).atTest T ≤ (splitBlock A (χ v) h).atTest T) ∧
      (F v).HasGeometricType q (a v)}

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups
