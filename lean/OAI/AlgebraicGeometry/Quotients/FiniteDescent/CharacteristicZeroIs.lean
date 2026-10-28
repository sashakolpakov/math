import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MultiplicationQuotient
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalPowerIn
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalUnramified
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Characteristic Zero Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CharacteristicZeroIs

/-!
# FiniteDescent over bases with residue characteristic zero

Multiplication by a unit is formally unramified, by the actual
infinitesimal group-point lifting lemmas. Properness makes it finite.
When every residue field has characteristic zero, every positive integer
is a unit in each base stalk, so the multiplication quotient construction
proves all conclusions of FiniteDescent over that base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.CharacteristicZero

theorem power_formallyUnramified {S : Scheme.{u}}
    (A : Over S) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x)) :
    FormallyUnramified ((𝟙 A : A ⟶ A) ^ n).left := by
  apply AbelianScheme.TorsionQuotient.LocalUnramified.LocalUnramifiedCriterion.of_local_hom_ext
  intro C hC J hJ a b hred hp
  let s := a ≫ A.hom
  have hb : b ≫ A.hom = s := by
    have h := congrArg (fun z => z ≫ A.hom) hp
    simpa only [Category.assoc, Over.w] using h.symm
  let α : Over.mk s ⟶ A := Over.homMk a rfl
  let β : Over.mk s ⟶ A := Over.homMk b hb
  have hp' : α ^ n = β ^ n := by
    apply Over.OverMorphism.ext
    change (α ≫ (𝟙 A : A ⟶ A) ^ n).left = (β ≫ (𝟙 A : A ⟶ A) ^ n).left at hp
    simpa only [MonObj.comp_pow, Category.comp_id] using hp
  have hred' : AbelianScheme.TorsionQuotient.LocalPowerIn.LocalPower.reduction s J A α =
      AbelianScheme.TorsionQuotient.LocalPowerIn.LocalPower.reduction s J A β := Over.OverMorphism.ext hred
  have hnC : IsUnit (n : C) := by
    simpa only [map_natCast] using
      (hn (s (IsLocalRing.closedPoint C))).map (Scheme.stalkClosedPointTo s).hom
  exact congrArg (fun z : Over.mk s ⟶ A => z.left)
    (AbelianScheme.TorsionQuotient.LocalPowerIn.LocalPower.power_lift_unique s J hJ A n hnC α β hred' hp')

theorem finite_of_proper_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [FormallyUnramified f] : IsFinite f := by
  have : LocallyQuasiFinite f := by
    constructor
    intro U hU V hV e
    let p := (f.appLE U V e).hom
    let : Algebra Γ(Y, U) Γ(X, V) := p.toAlgebra
    have : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) :=
      f.formallyUnramified_appLE hU hV e
    have : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV e
    exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

theorem finite_power_of_stalk_units {S : Scheme.{u}}
    (A : Over S) [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x)) :
    IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  have := RelativeFinitenessIs.Construction.RelativeFiniteness.power_isProper A n
  have := power_formallyUnramified A n hn
  exact finite_of_proper_formallyUnramified _

theorem natCast_stalk_isUnit (S : Scheme.{u})
    [∀ x : S, CharZero (S.residueField x)] (n : ℕ) (hn : 0 < n) (x : S) :
    IsUnit (n : S.presheaf.stalk x) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  change (n : S.residueField x) ≠ 0
  exact Nat.cast_ne_zero.mpr hn.ne'

end Construction.CharacteristicZero

theorem FiniteDescentProof.exists_abelian_scheme_quotient_of_residue_charZero
    (S : Scheme.{u}) [∀ x : S, CharZero (S.residueField x)]
    (A : AbelianQuotient.Construction.AbelianScheme S) (H : Over S) [GrpObj H]
    (i : H ⟶ A.toOver) [IsMonHom i]
    (hi : IsClosedImmersion i.left) (hH : AbelianQuotient.Construction.FiniteLocallyFree H.hom) :
    ∃ (B : AbelianQuotient.Construction.AbelianScheme S) (q : A.toOver ⟶ B.toOver),
      IsMonHom q ∧ AbelianQuotient.Construction.FiniteLocallyFree q.left ∧ Surjective q.left ∧
      (∀ (T : Over S) (a : T ⟶ A.toOver),
        a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) ∧
      (∀ (T : Over S) (f : A.toOver ⟶ T),
        (∀ (U : Over S) (a : U ⟶ A.toOver) (h : U ⟶ H),
          ((h ≫ i) * a) ≫ f = a ≫ f) →
        ∃! g : B.toOver ⟶ T, q ≫ g = f) := by
  apply MultiplicationQuotient.Construction.exists_abelian_scheme_quotient_of_finite_multiplication S A H i hi hH
  intro n hn
  exact Construction.CharacteristicZero.finite_power_of_stalk_units A.toOver n
    (Construction.CharacteristicZero.natCast_stalk_isUnit S n hn)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CharacteristicZeroIs
