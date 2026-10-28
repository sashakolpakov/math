import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeReduction
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricCubeIs

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Scheme.Construction

/-! FiniteDescent under the original abelian-scheme and finite locally free subgroup
hypotheses. The geometric cube identity closes the remaining multiplication
finiteness input in the relative quotient construction. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- Quotient of an abelian scheme by a finite locally free closed subgroup,
with finite locally free surjective projection, exact kernel on every test
scheme, and the universal property for invariant morphisms. -/
theorem exists_abelian_scheme_quotient
    (S : Scheme.{u}) (A : AbelianQuotient.Construction.AbelianScheme S)
    (H : Over S) [GrpObj H]
    (i : H ⟶ A.toOver) [IsMonHom i]
    (hi : IsClosedImmersion i.left)
    (hH : AbelianQuotient.Construction.FiniteLocallyFree H.hom) :
    ∃ (B : AbelianQuotient.Construction.AbelianScheme S) (q : A.toOver ⟶ B.toOver),
      IsMonHom q ∧
      AbelianQuotient.Construction.FiniteLocallyFree q.left ∧
      Surjective q.left ∧
      (∀ (T : Over S) (a : T ⟶ A.toOver),
        a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) ∧
      (∀ (T : Over S) (f : A.toOver ⟶ T),
        (∀ (U : Over S) (a : U ⟶ A.toOver) (h : U ⟶ H),
          ((h ≫ i) * a) ≫ f = a ≫ f) →
        ∃! g : B.toOver ⟶ T, q ≫ g = f) := by
  apply CubeReduction.Construction.exists_abelian_scheme_quotient_of_cubical_pullbacks _ S A H i hi hH
  intro K _ _ _ _ _ B L
  exact GeometricCubeIs.Construction.GeometricCubeIdentity.isCubical B.toOver L

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Scheme.Construction
