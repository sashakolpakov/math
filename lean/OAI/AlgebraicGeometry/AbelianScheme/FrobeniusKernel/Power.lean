import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientActionBase
import Mathlib.Data.Int.GCD

/-! # Power -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power.Construction

noncomputable section

/-!
Prime-to-q marking transport on every test scheme. Complementary isogenies
are obtained by fpqc descent of multiplication, and Bezout's identity gives
bijectivity on N-torsion. No geometric-point test discards nilpotents.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem power_bijective_on_torsion
    {G : Type*} [Group G] {n N : ℕ} (h : Nat.Coprime n N)
    (hN : ∀ x : G, x ^ N = 1) : Function.Bijective (fun x : G => x ^ n) := by
  have hbez : (n : ℤ) * Nat.gcdA n N + (N : ℤ) * Nat.gcdB n N = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one, Nat.cast_one]
  have hleft (x : G) : (x ^ n) ^ Nat.gcdA n N = x := by
    calc
      (x ^ n) ^ Nat.gcdA n N =
          (x ^ n) ^ Nat.gcdA n N * (x ^ N) ^ Nat.gcdB n N := by
            rw [hN, one_zpow, mul_one]
      _ = x ^ ((n : ℤ) * Nat.gcdA n N + (N : ℤ) * Nat.gcdB n N) := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = x := by rw [hbez, zpow_one]
  have hright (x : G) : (x ^ Nat.gcdA n N) ^ n = x := by
    calc
      (x ^ Nat.gcdA n N) ^ n = x ^ (Nat.gcdA n N * (n : ℤ)) := by
        rw [zpow_mul, zpow_natCast]
      _ = (x ^ n) ^ Nat.gcdA n N := by
        rw [mul_comm, zpow_mul, zpow_natCast]
      _ = x := hleft x
  exact ⟨Function.LeftInverse.injective hleft,
    Function.RightInverse.surjective hright⟩

theorem torsion_complement_bijective
    {G H : Type*} [Group G] [Group H] {n N : ℕ}
    (hnN : Nat.Coprime n N) (hG : ∀ x : G, x ^ N = 1) (hH : ∀ y : H, y ^ N = 1)
    (f : G →* H) (g : H →* G)
    (hgf : ∀ x, g (f x) = x ^ n) (hfg : ∀ y, f (g y) = y ^ n) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    apply (power_bijective_on_torsion hnN hG).1
    simpa only [hgf] using congrArg g hxy
  · intro y
    obtain ⟨z, hz⟩ := (power_bijective_on_torsion hnN hH).2 y
    exact ⟨g z, (hfg z).trans hz⟩

variable {S : Scheme.{u}} {g : ℕ}
variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

/-- The induced map on the full torsion group functors. -/
def torsionMap (p : A.scheme ⟶ B.scheme) [IsMonHom p] (N : ℕ) :
    A.torsionFunctor N ⟶ B.torsionFunctor N where
  app T := GrpCat.ofHom {
    toFun x := ⟨x.val ≫ p, by
      change (x.val ≫ p) ^ N = 1
      have hx : x.val ^ N = 1 := x.property
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]⟩
    map_one' := Subtype.ext (MonObj.one_comp p)
    map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val p) }
  naturality := by
    intro T U f
    apply GrpCat.hom_ext
    ext x
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- A q-power isogeny has an actual complementary group-scheme morphism. -/
theorem exists_complementary_isogeny_map
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ)
    (hkernel : ∀ (T : Over S) (x : T ⟶ A.scheme),
      x ≫ p.hom = 1 → x ^ n = 1) :
    ∃ d : B.scheme ⟶ A.scheme,
      IsMonHom d ∧ p.hom ≫ d = (𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n ∧
      d ≫ p.hom = (𝟙 B.scheme : B.scheme ⟶ B.scheme) ^ n := by
  obtain ⟨d, ⟨hd, hpd⟩, _⟩ :=
    PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.fpqc_multiple_descent p.hom (𝟙 A.scheme) n hkernel
  have : EffectiveEpi p.hom := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc p.hom
  refine ⟨d, hd, hpd, ?_⟩
  apply (cancel_epi p.hom).mp
  rw [← Category.assoc, hpd, MonObj.pow_comp, Category.id_comp,
    MonObj.comp_pow, Category.comp_id]

/-- The torsion map is bijective for every test scheme. -/
theorem torsionMap_bijective
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {n N : ℕ}
    (hnN : Nat.Coprime n N)
    (hkernel : ∀ (T : Over S) (x : T ⟶ A.scheme),
      x ≫ p.hom = 1 → x ^ n = 1) (T : (Over S)ᵒᵖ) :
    Function.Bijective ((torsionMap p.hom N).app T) := by
  obtain ⟨d, hd, hpd, hdp⟩ := exists_complementary_isogeny_map p n hkernel
  let : IsMonHom d := hd
  apply torsion_complement_bijective hnN
    (fun x => Subtype.ext x.property) (fun y => Subtype.ext y.property)
    ((torsionMap p.hom N).app T).hom ((torsionMap d N).app T).hom
  · intro x
    apply Subtype.ext
    change (x.val ≫ p.hom) ≫ d = x.val ^ n
    rw [Category.assoc, hpd, MonObj.comp_pow, Category.comp_id]
  · intro y
    apply Subtype.ext
    change (y.val ≫ d) ≫ p.hom = y.val ^ n
    rw [Category.assoc, hdp, MonObj.comp_pow, Category.comp_id]

def primeToIsogenyTorsionIso
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {n N : ℕ}
    (hnN : Nat.Coprime n N)
    (hkernel : ∀ (T : Over S) (x : T ⟶ A.scheme),
      x ≫ p.hom = 1 → x ^ n = 1) :
    A.torsionFunctor N ≅ B.torsionFunctor N :=
  NatIso.ofComponents
    (fun T => (MulEquiv.ofBijective ((torsionMap p.hom N).app T).hom
      (torsionMap_bijective p hnN hkernel T)).toGrpIso)
    (by intro T U f; exact (torsionMap p.hom N).naturality f)

/-- Construct the full marking on the quotient by transporting its basis
through the actual isogeny on N-torsion. -/
def quotientLevel
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {n N : ℕ}
    (hnN : Nat.Coprime n N)
    (hkernel : ∀ (T : Over S) (x : T ⟶ A.scheme),
      x ≫ p.hom = 1 → x ^ n = 1) (level : A.FullLevel N) : B.FullLevel N :=
  level.trans (primeToIsogenyTorsionIso p hnN hkernel)

theorem quotientLevel_transports
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {n N : ℕ}
    (hnN : Nat.Coprime n N)
    (hkernel : ∀ (T : Over S) (x : T ⟶ A.scheme),
      x ≫ p.hom = 1 → x ^ n = 1) (level : A.FullLevel N)
    (T : (Over S)ᵒᵖ) (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S).obj T) :
    ((quotientLevel p hnN hkernel level).hom.app T c).val =
      (level.hom.app T c).val ≫ p.hom := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power.Construction
