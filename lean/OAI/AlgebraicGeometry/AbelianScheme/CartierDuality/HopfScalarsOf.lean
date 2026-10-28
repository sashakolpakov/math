import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Hopf Scalars Of -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf

noncomputable section

/-!
# CartierDuality: actual regular scalar functions supplied by Hopf characters
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.HopfScalars

/-- The actual global section associated with an affine coordinate. -/
def coordinateSection (A : Type u) [CommRing A] (a : A) : Γ(Spec (.of A), ⊤) :=
  (Scheme.ΓSpecIso (.of A)).inv a

theorem coordinateSection_pullback {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom f)).appTop (coordinateSection A a) = coordinateSection B (f a) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) a).symm

/-- A scalar relation can be checked after an isomorphism of schemes. -/
theorem scalar_relation_of_iso {X Y Z : Scheme.{u}} (a : Z ⟶ X) [IsIso a]
    (m l r : X ⟶ Y) (s : Γ(Y, ⊤))
    (h : (a ≫ m).appTop s = (a ≫ l).appTop s * (a ≫ r).appTop s) :
    m.appTop s = l.appTop s * r.appTop s := by
  have : IsIso a.appTop := inferInstanceAs (IsIso (Scheme.Γ.map a.op))
  apply (ConcreteCategory.bijective_of_isIso a.appTop).injective
  exact h.trans (a.appTop.hom.map_mul _ _).symm

variable (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- A group-like coordinate has value one on the actual unit section. -/
theorem groupLikeScalar_unit (z : GroupLike R A) :
    η[(Spec (.of A)).asOver (Spec (.of R))].left.appTop (coordinateSection A z.val) = 1 := by
  have h := coordinateSection_pullback (Bialgebra.counitAlgHom R A).toRingHom z.val
  have hz : (Bialgebra.counitAlgHom R A) z.val = 1 := z.2.counit_eq_one
  exact h.trans ((congrArg (coordinateSection R) hz).trans (Scheme.ΓSpecIso (.of R)).inv.hom.map_one)

/-- The global group-like scalar is multiplicative on the actual
product scheme, by the Hopf comultiplication identity. -/
theorem groupLikeScalar_multiplication (z : GroupLike R A) :
    μ[(Spec (.of A)).asOver (Spec (.of R))].left.appTop (coordinateSection A z.val) =
      (fst ((Spec (.of A)).asOver (Spec (.of R))) ((Spec (.of A)).asOver (Spec (.of R)))).left.appTop
          (coordinateSection A z.val) *
        (snd ((Spec (.of A)).asOver (Spec (.of R))) ((Spec (.of A)).asOver (Spec (.of R)))).left.appTop
          (coordinateSection A z.val) := by
  let e := pullbackSpecIso R A A
  apply scalar_relation_of_iso e.inv
  have hm : e.inv ≫ μ[(Spec (.of A)).asOver (Spec (.of R))].left =
      Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R A).toRingHom) := by
    rw [mul_spec_asOver_spec_left]
    exact e.inv_hom_id_assoc _
  have hl : e.inv ≫
      (fst ((Spec (.of A)).asOver (Spec (.of R))) ((Spec (.of A)).asOver (Spec (.of R)))).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)) :=
    pullbackSpecIso_inv_fst R A A
  have hr : e.inv ≫
      (snd ((Spec (.of A)).asOver (Spec (.of R))) ((Spec (.of A)).asOver (Spec (.of R)))).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom) :=
    pullbackSpecIso_inv_snd R A A
  have hm' := (congrArg (fun f => f.appTop (coordinateSection A z.val)) hm).trans
    (coordinateSection_pullback (Bialgebra.comulAlgHom R A).toRingHom z.val)
  have hl' := (congrArg (fun f => f.appTop (coordinateSection A z.val)) hl).trans
    (coordinateSection_pullback (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) z.val)
  have hr' := (congrArg (fun f => f.appTop (coordinateSection A z.val)) hr).trans
    (coordinateSection_pullback (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom z.val)
  have hz : (Bialgebra.comulAlgHom R A) z.val = z.val ⊗ₜ[R] z.val := z.2.comul_eq_tmul_self
  have ht : (z.val ⊗ₜ[R] 1) * (1 ⊗ₜ[R] z.val) = z.val ⊗ₜ[R] z.val := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hc := (congrArg (coordinateSection (A ⊗[R] A)) hz).trans
    ((congrArg (coordinateSection (A ⊗[R] A)) ht.symm).trans
      ((Scheme.ΓSpecIso (.of (A ⊗[R] A))).inv.hom.map_mul _ _))
  exact hm'.trans (hc.trans (congrArg₂ (· * ·) hl'.symm hr'.symm))

/-- The scalar character is multiplicative on every test scheme,
including nonreduced and nonaffine test schemes. -/
theorem groupLikeScalar_points_mul (z : GroupLike R A) (T : Over (Spec (.of R)))
    (x y : T ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    (x * y).left.appTop (coordinateSection A z.val) =
      x.left.appTop (coordinateSection A z.val) * y.left.appTop (coordinateSection A z.val) := by
  let G := (Spec (.of A)).asOver (Spec (.of R))
  let q : T ⟶ G ⊗ G := lift x y
  have hm : (x * y).left = q.left ≫ μ[G].left := rfl
  have hl : q.left ≫ (fst G G).left = x.left := congrArg Over.Hom.left (lift_fst x y)
  have hr : q.left ≫ (snd G G).left = y.left := congrArg Over.Hom.left (lift_snd x y)
  rw [hm]
  change q.left.appTop (μ[G].left.appTop (coordinateSection A z.val)) = _
  rw [groupLikeScalar_multiplication, map_mul]
  exact congrArg₂ (· * ·)
    (congrArg (fun f => f.appTop (coordinateSection A z.val)) hl)
    (congrArg (fun f => f.appTop (coordinateSection A z.val)) hr)

theorem groupLikeScalar_points_one (z : GroupLike R A) (T : Over (Spec (.of R))) :
    (1 : T ⟶ (Spec (.of A)).asOver (Spec (.of R))).left.appTop (coordinateSection A z.val) = 1 := by
  change (toUnit T).left.appTop
    (η[(Spec (.of A)).asOver (Spec (.of R))].left.appTop (coordinateSection A z.val)) = 1
  rw [groupLikeScalar_unit, map_one]

/-- The value of a Hopf character is an actual unit; its inverse is
the value at the inverse test-scheme point. -/
def groupLikeUnitValue (z : GroupLike R A) (T : Over (Spec (.of R)))
    (x : T ⟶ (Spec (.of A)).asOver (Spec (.of R))) : Γ(T.left, ⊤)ˣ where
  val := x.left.appTop (coordinateSection A z.val)
  inv := x⁻¹.left.appTop (coordinateSection A z.val)
  val_inv := (groupLikeScalar_points_mul R A z T x x⁻¹).symm.trans
    ((congrArg (fun q => q.left.appTop (coordinateSection A z.val)) (mul_inv_cancel x)).trans
      (groupLikeScalar_points_one R A z T))
  inv_val := (groupLikeScalar_points_mul R A z T x⁻¹ x).symm.trans
    ((congrArg (fun q => q.left.appTop (coordinateSection A z.val)) (inv_mul_cancel x)).trans
      (groupLikeScalar_points_one R A z T))

/-- A Hopf character gives a homomorphism into the units of the actual
global functions on each test scheme. -/
def groupLikeUnitHom (z : GroupLike R A) (T : Over (Spec (.of R))) :
    (T ⟶ (Spec (.of A)).asOver (Spec (.of R))) →* Γ(T.left, ⊤)ˣ where
  toFun := groupLikeUnitValue R A z T
  map_one' := Units.ext (groupLikeScalar_points_one R A z T)
  map_mul' x y := Units.ext (groupLikeScalar_points_mul R A z T x y)

theorem groupLikeUnitHom_natural (z : GroupLike R A) {T U : Over (Spec (.of R))}
    (t : U ⟶ T) (x : T ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    Units.map t.left.appTop.hom (groupLikeUnitHom R A z T x) =
      groupLikeUnitHom R A z U (t ≫ x) := Units.ext rfl

/-- The constructed regular scalar is exactly the Laurent-generator
value of the actual native group-scheme character. -/
theorem groupLikeUnitValue_native (z : GroupLike R A) (T : Over (Spec (.of R)))
    (x : T ⟶ (Characters.Construction.affineHopfGroupScheme R A).X) :
    (x ≫ (Characters.Construction.groupLikeEquivSchemeCharacters R A z).hom.hom).left.appTop
      (coordinateSection (Characters.Construction.MultiplicativeGroupCoordinate R)
        (MonoidAlgebra.of R (Multiplicative ℤ) (Multiplicative.ofAdd 1))) =
      (groupLikeUnitHom R A z T x).val := by
  have h := coordinateSection_pullback (Characters.Construction.groupLikeEquivHopfCharacters R A z).toAlgHom.toRingHom
    (MonoidAlgebra.of R (Multiplicative ℤ) (Multiplicative.ofAdd 1))
  have hv := congrArg (coordinateSection A) (Characters.Construction.groupLikeEquivHopfCharacters_generator R A z)
  exact congrArg x.left.appTop (h.trans hv)

end Construction.HopfScalars

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf
