import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Prime To Degree Torsion -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PrimeToDegreeTorsion

noncomputable section

/-! Actual inverse maps up to an integer scalar induce torsion
isomorphisms whenever that integer is coprime to the torsion order.
This is the isogeny comparison needed for CM products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def powerEquiv_of_exponent {G : Type*} [Group G] (N d : ℕ) (h : N.Coprime d)
    (hN : ∀ x : G, x ^ N = 1) : G ≃ G where
  toFun x := x ^ d
  invFun x := x ^ N.gcdB d
  left_inv x := by
    have key := congrArg (x ^ ·) (N.gcd_eq_gcd_ab d)
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast,
      h.gcd_eq_one, pow_one, hN, one_zpow, one_mul, eq_comm] at key
  right_inv x := by
    have key := congrArg (x ^ ·) (N.gcd_eq_gcd_ab d)
    rwa [zpow_add, zpow_mul, zpow_mul', zpow_natCast, zpow_natCast, zpow_natCast,
      h.gcd_eq_one, pow_one, hN, one_zpow, one_mul, eq_comm] at key

theorem bijective_of_scalar_composites {G H : Type*} [Group G] [Group H]
    (f : G → H) (h : H → G) (N d : ℕ) (hcop : N.Coprime d)
    (hG : ∀ x : G, x ^ N = 1) (hH : ∀ x : H, x ^ N = 1)
    (hgf : ∀ x, h (f x) = x ^ d) (hfg : ∀ y, f (h y) = y ^ d) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    apply (powerEquiv_of_exponent N d hcop hG).injective
    exact (hgf x).symm.trans ((congrArg h hxy).trans (hgf y))
  · intro y
    obtain ⟨z, hz⟩ := (powerEquiv_of_exponent N d hcop hH).surjective y
    exact ⟨h z, (hfg z).trans hz⟩

variable {S : Scheme.{0}} {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (f : A.scheme ⟶ B.scheme) (h : B.scheme ⟶ A.scheme) [IsMonHom f] [IsMonHom h]

theorem homOnTorsion_isIso_of_scalar_inverse (N d : ℕ) (hcop : N.Coprime d)
    (hgf : f ≫ h = A.multiplication d) (hfg : h ≫ f = B.multiplication d) :
    IsIso (DualityPairing.homOnTorsion A B f N) := by
  have hcompA (T : Over S) (x : A.torsionPoints N T) :
      (DualityPairing.homOnTorsion B A h N).app (.op T) ((DualityPairing.homOnTorsion A B f N).app (.op T) x) = x ^ d := by
    apply Subtype.ext
    change (x.val ≫ f) ≫ h = x.val ^ d
    rw [Category.assoc, hgf]
    simp only [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.multiplication, MonObj.comp_pow, Category.comp_id]
  have hcompB (T : Over S) (x : B.torsionPoints N T) :
      (DualityPairing.homOnTorsion A B f N).app (.op T) ((DualityPairing.homOnTorsion B A h N).app (.op T) x) = x ^ d := by
    apply Subtype.ext
    change (x.val ≫ h) ≫ f = x.val ^ d
    rw [Category.assoc, hfg]
    simp only [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.multiplication, MonObj.comp_pow, Category.comp_id]
  have hG (T : Over S) (x : A.torsionPoints N T) : x ^ N = 1 := Subtype.ext x.property
  have hH (T : Over S) (x : B.torsionPoints N T) : x ^ N = 1 := Subtype.ext x.property
  have (T : (Over S)ᵒᵖ) : IsIso ((DualityPairing.homOnTorsion A B f N).app T) := by
    have hb := bijective_of_scalar_composites ((DualityPairing.homOnTorsion A B f N).app T)
      ((DualityPairing.homOnTorsion B A h N).app T) N d hcop (hG T.unop) (hH T.unop)
      (hcompA T.unop) (hcompB T.unop)
    exact (MulEquiv.toGrpIso (MulEquiv.ofBijective ((DualityPairing.homOnTorsion A B f N).app T).hom hb)).isIso_hom
  exact NatIso.isIso_of_isIso_app _

def torsionIso_of_scalar_inverse (N d : ℕ) (hcop : N.Coprime d)
    (hgf : f ≫ h = A.multiplication d) (hfg : h ≫ f = B.multiplication d) :
    A.torsionFunctor N ≅ B.torsionFunctor N := by
  let := homOnTorsion_isIso_of_scalar_inverse A B f h N d hcop hgf hfg
  exact asIso (DualityPairing.homOnTorsion A B f N)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PrimeToDegreeTorsion
