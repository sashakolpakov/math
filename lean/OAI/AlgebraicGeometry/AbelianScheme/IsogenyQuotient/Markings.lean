import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies
import Mathlib.Data.Int.GCD

/-! # Markings -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Markings.Construction

noncomputable section

/-!
Transport of the actual full-level functor used by ReferenceFamily. Complementary
isogenies induce an isomorphism on all N-torsion test-scheme groups when
the multiplier is prime to N. Composition transports every ordered full
marking, without restricting its similitude component.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem torsion_bezout_inverse
    {G : Type*} [Group G] (n N : ℕ) (hcop : Nat.Coprime n N)
    (x : G) (hx : x ^ N = 1) : (x ^ n) ^ (Nat.gcdA n N) = x := by
  have h := congrArg (fun z : ℤ => x ^ z) (Nat.gcd_eq_gcd_ab n N)
  simpa only [hcop, Nat.cast_one, zpow_one, zpow_add, zpow_mul,
    zpow_natCast, hx, one_zpow, mul_one] using h.symm

variable {S : Scheme.{u}} {g₁ g₂ : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g₁ S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g₂ S)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

def torsionPointMap (N : ℕ) (T : Over S) :
    A.torsionPoints N T →* B.torsionPoints N T where
  toFun x := ⟨x.val ≫ f, by
    change (x.val ≫ f) ^ N = 1
    rw [← MonObj.pow_comp, show x.val ^ N = 1 from x.property, MonObj.one_comp]⟩
  map_one' := Subtype.ext (MonObj.one_comp f)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val f)

theorem torsionPointMap_bijective
    (back : B.scheme ⟶ A.scheme) [IsMonHom back]
    (n N : ℕ) (hcop : Nat.Coprime n N)
    (hfb : f ≫ back = (𝟙 A.scheme) ^ n)
    (hbf : back ≫ f = (𝟙 B.scheme) ^ n) (T : Over S) :
    Function.Bijective (torsionPointMap A B f N T) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z => z.val ≫ back) hxy
    change (x.val ≫ f) ≫ back = (y.val ≫ f) ≫ back at h
    simp only [Category.assoc, hfb, MonObj.comp_pow, Category.comp_id] at h
    rw [← torsion_bezout_inverse n N hcop x.val x.property,
      ← torsion_bezout_inverse n N hcop y.val y.property, h]
  · intro y
    let x := (torsionPointMap B A back N T y) ^ (Nat.gcdA n N)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (((y.val ≫ back) ^ (Nat.gcdA n N)) ≫ f) = y.val
    rw [GrpObj.zpow_comp, Category.assoc, hbf, MonObj.comp_pow, Category.comp_id]
    exact torsion_bezout_inverse n N hcop y.val y.property

def torsionFunctorMap (N : ℕ) : A.torsionFunctor N ⟶ B.torsionFunctor N where
  app T := GrpCat.ofHom (torsionPointMap A B f N T.unop)
  naturality _ _ t := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact Category.assoc t.unop x.val f

/-- The actual torsion functor isomorphism, natural on all test schemes. -/
def torsionFunctorIso
    (back : B.scheme ⟶ A.scheme) [IsMonHom back]
    (n N : ℕ) (hcop : Nat.Coprime n N)
    (hfb : f ≫ back = (𝟙 A.scheme) ^ n)
    (hbf : back ≫ f = (𝟙 B.scheme) ^ n) :
    A.torsionFunctor N ≅ B.torsionFunctor N := by
  let t := torsionFunctorMap A B f N
  have : ∀ T, IsIso (t.app T) := fun T => by
    let e : (A.torsionFunctor N).obj T ≃* (B.torsionFunctor N).obj T :=
      MulEquiv.ofBijective (torsionPointMap A B f N T.unop)
        (torsionPointMap_bijective A B f back n N hcop hfb hbf T.unop)
    exact e.toGrpIso.isIso_hom
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- Transport any full ordered marking by the quotient isogeny. -/
def transportFullLevel
    {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (back : B.scheme ⟶ A.scheme) [IsMonHom back]
    (n N : ℕ) (hcop : Nat.Coprime n N)
    (hfb : f ≫ back = (𝟙 A.scheme) ^ n)
    (hbf : back ≫ f = (𝟙 B.scheme) ^ n)
    (level : A.FullLevel N) : B.FullLevel N :=
  level ≪≫ torsionFunctorIso A B f back n N hcop hfb hbf

theorem transportFullLevel_apply
    {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (back : B.scheme ⟶ A.scheme) [IsMonHom back]
    (n N : ℕ) (hcop : Nat.Coprime n N)
    (hfb : f ≫ back = (𝟙 A.scheme) ^ n)
    (hbf : back ≫ f = (𝟙 B.scheme) ^ n)
    (level : A.FullLevel N) (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (((transportFullLevel A B f back n N hcop hfb hbf level).hom.app (.op T)) c).val =
      ((level.hom.app (.op T)) c).val ≫ f := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Markings.Construction
