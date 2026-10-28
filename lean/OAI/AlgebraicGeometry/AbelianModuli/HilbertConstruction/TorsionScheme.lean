import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Torsion Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A concrete scheme representing the torsion points of an abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S : Scheme.{u}}

/-- Multiplication by a natural number on an abelian scheme. -/
def Abelian.Schemes.AbelianScheme.multiplication (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) : A.scheme ⟶ A.scheme :=
  (𝟙 A.scheme : A.Points A.scheme) ^ N

@[simp]
theorem Abelian.Schemes.AbelianScheme.comp_multiplication (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) {T : Over S}
    (x : A.Points T) : x ≫ A.multiplication N = x ^ N := by
  simp only [Abelian.Schemes.AbelianScheme.multiplication, MonObj.comp_pow, Category.comp_id]

theorem Abelian.Schemes.AbelianScheme.one_point_left (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    (1 : A.Points T).left = T.hom ≫ η[A.scheme].left := rfl

/-- The torsion condition is the scheme-theoretic zero-fiber equation. -/
theorem Abelian.Schemes.AbelianScheme.torsion_condition_iff (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) (T : Over S)
    (x : A.Points T) :
    x.left ≫ (A.multiplication N).left = T.hom ≫ η[A.scheme].left ↔ x ^ N = 1 := by
  rw [← A.comp_multiplication N x]
  constructor
  · intro w
    exact Over.OverMorphism.ext w
  · intro w
    exact congrArg (fun a : A.Points T => a.left) w

/-- The zero fiber of multiplication by `N`, with its map to the base. -/
def Abelian.Schemes.AbelianScheme.torsionScheme (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) : Over S :=
  Over.mk (pullback.snd (A.multiplication N).left η[A.scheme].left)

/-- The inclusion of the torsion scheme into the original abelian scheme. -/
def Abelian.Schemes.AbelianScheme.torsionInclusion (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) : A.torsionScheme N ⟶ A.scheme :=
  Over.homMk (pullback.fst (A.multiplication N).left η[A.scheme].left) (by
    have hn := (A.multiplication N).w
    have hz := η[A.scheme].w
    change η[A.scheme].left ≫ A.scheme.hom = 𝟙 S at hz
    calc
      _ = pullback.fst (A.multiplication N).left η[A.scheme].left ≫
          (A.multiplication N).left ≫ A.scheme.hom := congrArg (fun a => _ ≫ a) hn.symm
      _ = pullback.snd (A.multiplication N).left η[A.scheme].left ≫
          η[A.scheme].left ≫ A.scheme.hom := pullback.condition_assoc A.scheme.hom
      _ = _ := (congrArg (fun a =>
        pullback.snd (A.multiplication N).left η[A.scheme].left ≫ a) hz).trans
          (Category.comp_id _))

/-- Multiplication is proper because both its domain and codomain are proper over the base. -/
instance Abelian.Schemes.AbelianScheme.multiplication_proper (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    IsProper (A.multiplication N).left := by
  have : IsProper ((A.multiplication N).left ≫ A.scheme.hom) := by
    rw [(A.multiplication N).w]
    infer_instance
  exact IsProper.of_comp _ A.scheme.hom

/-- The scheme of `N`-torsion points is proper over the base. -/
instance Abelian.Schemes.AbelianScheme.torsionScheme_proper (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    IsProper (A.torsionScheme N).hom :=
  inferInstanceAs (IsProper (pullback.snd (A.multiplication N).left η[A.scheme].left))

/-- The universal point of the zero fiber is killed by `N`. -/
theorem Abelian.Schemes.AbelianScheme.torsionInclusion_pow (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    A.torsionInclusion N ^ N = 1 :=
  (A.torsion_condition_iff N (A.torsionScheme N) (A.torsionInclusion N)).mp
    pullback.condition

/-- Morphisms into the zero fiber are precisely torsion points. -/
def Abelian.Schemes.AbelianScheme.torsionSchemePointsEquiv (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) (T : Over S) :
    (T ⟶ A.torsionScheme N) ≃ A.torsionPoints N T where
  toFun t := ⟨t ≫ A.torsionInclusion N, by
    change (t ≫ A.torsionInclusion N) ^ N = 1
    rw [← MonObj.comp_pow, A.torsionInclusion_pow, MonObj.comp_one]⟩
  invFun x := Over.homMk
    (pullback.lift x.val.left T.hom ((A.torsion_condition_iff N T x.val).mpr x.property))
    (pullback.lift_snd _ _ _)
  left_inv t := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans t.w.symm
  right_inv x := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- The concrete torsion scheme represents the previously defined torsion functor. -/
def Abelian.Schemes.AbelianScheme.torsionRepresentable (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    (A.torsionFunctor N ⋙ forget GrpCat).RepresentableBy (A.torsionScheme N) where
  homEquiv := A.torsionSchemePointsEquiv N _
  homEquiv_comp h t := by
    apply Subtype.ext
    exact Category.assoc h t (A.torsionInclusion N)

/-- The represented group law makes the zero fiber a group scheme. -/
instance Abelian.Schemes.AbelianScheme.torsionScheme_group (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    GrpObj (A.torsionScheme N) :=
  GrpObj.ofRepresentableBy (A.torsionScheme N) (A.torsionFunctor N) (A.torsionRepresentable N)

/-- The representing equivalence preserves the group structure on points. -/
def Abelian.Schemes.AbelianScheme.torsionSchemeYonedaIso (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    yonedaGrpObj (A.torsionScheme N) ≅ A.torsionFunctor N :=
  yonedaGrpObjIsoOfRepresentableBy (A.torsionScheme N) (A.torsionFunctor N)
    (A.torsionRepresentable N)

/-- The represented torsion group scheme is commutative. -/
instance Abelian.Schemes.AbelianScheme.torsionScheme_commutative (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    IsCommMonObj (A.torsionScheme N) := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (A.torsionSchemePointsEquiv N T).injective
  exact (((A.torsionSchemeYonedaIso N).hom.app (.op T)).hom.map_mul x y).trans
    ((mul_comm (A.torsionSchemePointsEquiv N T x) (A.torsionSchemePointsEquiv N T y)).trans
      (((A.torsionSchemeYonedaIso N).hom.app (.op T)).hom.map_mul y x).symm)

/-- The unit section of an abelian scheme is a closed immersion. -/
instance Abelian.Schemes.AbelianScheme.unit_closedImmersion (A : Abelian.Schemes.AbelianScheme g S) :
    IsClosedImmersion η[A.scheme].left := by
  have : IsClosedImmersion (η[A.scheme].left ≫ A.scheme.hom) := by
    rw [η[A.scheme].w]
    exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  exact IsClosedImmersion.of_comp _ A.scheme.hom

/-- The torsion group scheme is a closed subscheme of the abelian scheme. -/
instance Abelian.Schemes.AbelianScheme.torsionInclusion_closedImmersion (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    IsClosedImmersion (A.torsionInclusion N).left :=
  inferInstanceAs (IsClosedImmersion (pullback.fst (A.multiplication N).left η[A.scheme].left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
