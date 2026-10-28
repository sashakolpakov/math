import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Abelian Products -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianProducts

noncomputable section

section

/-! Products of the actual abelian schemes, with additive relative
dimension and the product decomposition of every torsion functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g h : ℕ}

def abelianProduct (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (g + h) S where
  scheme := A.scheme ⊗ B.scheme
  group := inferInstance
  commutative := inferInstance
  proper := inferInstanceAs
    (IsProper (CategoryTheory.Limits.pullback.fst A.scheme.hom B.scheme.hom ≫ A.scheme.hom))
  smoothDimension := by
    let F := CategoryTheory.Limits.pullback.fst A.scheme.hom B.scheme.hom
    have : SmoothOfRelativeDimension h F :=
      (smoothOfRelativeDimension_isStableUnderBaseChange h).of_isPullback
        (CategoryTheory.IsPullback.of_hasPullback A.scheme.hom B.scheme.hom).flip B.smoothDimension
    have hh : SmoothOfRelativeDimension (h + g) (F ≫ A.scheme.hom) := inferInstance
    rw [Nat.add_comm h g] at hh
    exact hh
  connected := GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst A.scheme.hom B.scheme.hom) A.scheme.hom

def groupProductTorsionEquiv (X Y : Over S) [GrpObj X] [GrpObj Y]
    [IsCommMonObj X] [IsCommMonObj Y] (N : ℕ) (T : Over S) :
    ((powMonoidHom N : (T ⟶ X ⊗ Y) →* (T ⟶ X ⊗ Y)).ker) ≃*
      (((powMonoidHom N : (T ⟶ X) →* (T ⟶ X)).ker) ×
        ((powMonoidHom N : (T ⟶ Y) →* (T ⟶ Y)).ker)) where
  toFun x := (⟨x.val ≫ fst X Y, by
      change (x.val ≫ fst X Y) ^ N = 1
      have hx : x.val ^ N = 1 := x.property
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]⟩,
    ⟨x.val ≫ snd X Y, by
      change (x.val ≫ snd X Y) ^ N = 1
      have hx : x.val ^ N = 1 := x.property
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]⟩)
  invFun x := ⟨lift x.1.val x.2.val, by
    change (lift x.1.val x.2.val) ^ N = 1
    have hx : x.1.val ^ N = 1 := x.1.property
    have hy : x.2.val ^ N = 1 := x.2.property
    apply hom_ext
    · rw [MonObj.pow_comp, lift_fst, hx, MonObj.one_comp]
    · rw [MonObj.pow_comp, lift_snd, hy, MonObj.one_comp]⟩
  left_inv x := by
    apply Subtype.ext
    apply hom_ext
    · exact lift_fst _ _
    · exact lift_snd _ _
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext
    · exact lift_fst _ _
    · exact lift_snd _ _
  map_mul' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact MonObj.mul_comp x.val y.val _
    · exact MonObj.mul_comp x.val y.val _

def abelianProductTorsionEquiv (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (N : ℕ) (T : Over S) :
    (abelianProduct A B).torsionPoints N T ≃*
      (A.torsionPoints N T × B.torsionPoints N T) :=
  groupProductTorsionEquiv A.scheme B.scheme N T

end

/-! A finite family of abelian schemes embeds as retracts of one abelian
scheme. This lets all arrows be encoded as a finite endomorphism tuple. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem constantOne_isMonHom {C : Type*} [Category C] [CartesianMonoidalCategory C]
    (X Y : C) [MonObj X] [MonObj Y] : IsMonHom (1 : X ⟶ Y) :=
  inferInstanceAs (IsMonHom (toUnit X ≫ η[Y]))

def zeroAbelianScheme (S : Scheme.{0}) : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme 0 S where
  scheme := 𝟙_ (Over S)
  group := inferInstance
  commutative := inferInstance
  proper := inferInstanceAs (IsProper (𝟙 S))
  smoothDimension := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 S))
  connected := by
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
    exact (asIso (CategoryTheory.Limits.pullback.snd (𝟙 S) x)).hom.homeomorph.connectedSpace_iff.mpr
      inferInstance

structure AbelianRetractContainer {S : Scheme.{0}} {r : ℕ} {d : Fin r → ℕ}
    (A : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S) where
  dimension : ℕ
  abelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dimension S
  inclusion : ∀ i, (A i).scheme ⟶ abelian.scheme
  projection : ∀ i, abelian.scheme ⟶ (A i).scheme
  inclusion_group : ∀ i, IsMonHom (inclusion i)
  projection_group : ∀ i, IsMonHom (projection i)
  retraction : ∀ i, inclusion i ≫ projection i = 𝟙 (A i).scheme

theorem exists_abelian_retract_container {S : Scheme.{0}} (r : ℕ)
    (d : Fin r → ℕ) (A : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S) :
    Nonempty (AbelianRetractContainer A) := by
  induction r with
  | zero =>
    exact ⟨{
      dimension := 0
      abelian := zeroAbelianScheme S
      inclusion := fun i => Fin.elim0 i
      projection := fun i => Fin.elim0 i
      inclusion_group := fun i => Fin.elim0 i
      projection_group := fun i => Fin.elim0 i
      retraction := fun i => Fin.elim0 i }⟩
  | succ r ih =>
    obtain ⟨C⟩ := ih (fun i => d i.succ) (fun i => A i.succ)
    let B := abelianProduct (A 0) C.abelian
    let i₀ : (A 0).scheme ⟶ B.scheme := lift (𝟙 _) 1
    let it (j : Fin r) : (A j.succ).scheme ⟶ B.scheme := lift 1 (C.inclusion j)
    let p₀ : B.scheme ⟶ (A 0).scheme := fst _ _
    let pt (j : Fin r) : B.scheme ⟶ (A j.succ).scheme := snd _ _ ≫ C.projection j
    refine ⟨{
      dimension := d 0 + C.dimension
      abelian := B
      inclusion := Fin.cases i₀ it
      projection := Fin.cases p₀ pt
      inclusion_group := ?_
      projection_group := ?_
      retraction := ?_ }⟩
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · have := constantOne_isMonHom (A 0).scheme C.abelian.scheme
        exact inferInstanceAs (IsMonHom (lift (𝟙 (A 0).scheme) (1 : (A 0).scheme ⟶ C.abelian.scheme)))
      · have := C.inclusion_group k
        have := constantOne_isMonHom (A k.succ).scheme (A 0).scheme
        exact inferInstanceAs (IsMonHom (lift (1 : (A k.succ).scheme ⟶ (A 0).scheme) (C.inclusion k)))
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact inferInstanceAs (IsMonHom (fst (A 0).scheme C.abelian.scheme))
      · have := C.projection_group k
        exact inferInstanceAs (IsMonHom (snd (A 0).scheme C.abelian.scheme ≫ C.projection k))
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact lift_fst _ _
      · change lift 1 (C.inclusion k) ≫ snd _ _ ≫ C.projection k = _
        rw [← Category.assoc, lift_snd]
        exact C.retraction k

theorem recover_arrow_from_retracts {C : Type*} [Category C]
    {A B P : C} (iA : A ⟶ P) (pA : P ⟶ A) (iB : B ⟶ P) (pB : P ⟶ B)
    (hA : iA ≫ pA = 𝟙 A) (hB : iB ≫ pB = 𝟙 B) (f : A ⟶ B) :
    iA ≫ (pA ≫ f ≫ iB) ≫ pB = f := by
  simp only [Category.assoc, ← Category.assoc iA pA, hA, Category.id_comp,
    hB, Category.comp_id]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianProducts
