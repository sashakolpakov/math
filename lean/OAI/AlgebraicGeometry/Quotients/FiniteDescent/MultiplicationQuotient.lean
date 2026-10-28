import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFinitenessIs

/-! # Multiplication Quotient -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent

/-!
# The relative quotient from finiteness of multiplication

The subgroup annihilator is constructed pointwise in `PowerOrbit`; no
scheme-theoretic annihilator hypothesis is needed. Relative finiteness then
reduces the remaining geometric input to multiplication over fields.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

noncomputable def AbelianQuotient.Construction.AbelianScheme.baseChange {S T : Scheme.{u}}
    (A : AbelianQuotient.Construction.AbelianScheme S) (f : T ⟶ S) : AbelianQuotient.Construction.AbelianScheme T where
  toOver := (Over.pullback f).obj A.toOver
  group := Functor.grpObjObj
  commutative := inferInstance
  proper := inferInstanceAs (IsProper (Limits.pullback.snd A.toOver.hom f))
  smooth := inferInstanceAs (Smooth (Limits.pullback.snd A.toOver.hom f))
  connected := inferInstanceAs (GeometricallyConnected (Limits.pullback.snd A.toOver.hom f))

theorem MultiplicationQuotient.Construction.exists_abelian_scheme_quotient_of_finite_multiplication
    (S : Scheme.{u}) (A : AbelianQuotient.Construction.AbelianScheme S) (H : Over S) [GrpObj H]
    (i : H ⟶ A.toOver) [IsMonHom i]
    (hi : IsClosedImmersion i.left) (hH : AbelianQuotient.Construction.FiniteLocallyFree H.hom)
    (hpow : ∀ n : ℕ, 0 < n → IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left) :
    ∃ (B : AbelianQuotient.Construction.AbelianScheme S) (q : A.toOver ⟶ B.toOver),
      IsMonHom q ∧ AbelianQuotient.Construction.FiniteLocallyFree q.left ∧ Surjective q.left ∧
      (∀ (T : Over S) (a : T ⟶ A.toOver),
        a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) ∧
      (∀ (T : Over S) (f : A.toOver ⟶ T),
        (∀ (U : Over S) (a : U ⟶ A.toOver) (h : U ⟶ H),
          ((h ≫ i) * a) ≫ f = a ≫ f) →
        ∃! g : B.toOver ⟶ T, q ≫ g = f) := by
  have : IsFinite H.hom := hH.1
  exact AbelianQuotient.Construction.exists_abelian_scheme_quotient_of_affine_orbits S A H i hi hH
    (PowerOrbitEq.Construction.PowerOrbit.exists_affine_orbit_of_finite_powers i hpow)

/-- A reduction to the independent finiteness theorem for multiplication
on abelian varieties. The field finiteness input remains explicit. -/
theorem MultiplicationQuotient.Construction.exists_abelian_scheme_quotient_of_field_multiplication
    (hfield : ∀ (K : Type u) [Field K] (B : AbelianQuotient.Construction.AbelianScheme (Spec (.of K)))
      (n : ℕ), 0 < n → IsFinite ((𝟙 B.toOver : B.toOver ⟶ B.toOver) ^ n).left)
    (S : Scheme.{u}) (A : AbelianQuotient.Construction.AbelianScheme S) (H : Over S) [GrpObj H]
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
  apply RelativeFinitenessIs.Construction.RelativeFiniteness.finite_power_of_field_powers A.toOver n
  intro K _ a
  exact hfield K (A.baseChange a) n hn

end OAI.AlgebraicGeometry.Quotients.FiniteDescent
