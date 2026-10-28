import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubicalMultiplicationIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PrimeReductionOf

/-! # Cube Reduction -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeReduction.Construction

/-! The interface from the geometric cube identity to the relative FiniteDescent
quotient construction. `GeometricCubeIdentity` proves the input and
`FiniteDescentFinal` applies this reduction under the original hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The cube identity for actual line-bundle classes supplies the final
multiplication-finiteness input to the relative quotient construction. -/
theorem exists_abelian_scheme_quotient_of_cubical_pullbacks
    (hcube : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
      (B : AbelianQuotient.Construction.AbelianScheme (Spec (.of K))) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.toOver.left),
      CubicalMultiplicationIs.Construction.CubicalMultiplication.IsCubical B.toOver L)
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
  apply PrimeReductionOf.Construction.exists_abelian_scheme_quotient_of_characteristic_prime_finiteness _ S A H i hi hH
  intro K _ _ p hp _ B
  exact CubicalMultiplicationIs.Construction.CubicalMultiplication.isFinite B.toOver (hcube K p B) p hp.out.pos

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeReduction.Construction
