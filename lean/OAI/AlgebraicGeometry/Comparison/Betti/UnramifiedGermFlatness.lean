import OAI.AlgebraicGeometry.Comparison.Betti.MultivariableGermFlatness
import Mathlib.RingTheory.Unramified.Finite

/-! # Unramified Germ Flatness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.UnramifiedGermFlatness.AnalyticLocal

noncomputable section

/-! The proved polynomial germ flatness passes to an unramified
coordinate algebra whenever the actual evaluation maps commute. -/

theorem flat_of_unramified_composite {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A]
    (g : A →+* B) (hg : (g.comp (algebraMap R A)).Flat) : g.Flat := by
  let : Algebra A B := g.toAlgebra
  let : Algebra R B := (g.comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Flat R B := hg
  exact Algebra.FormallyUnramified.flat_of_restrictScalars R A B

theorem unramified_germ_map_flat {n : ℕ} (x : Fin n → ℂ)
    {A : Type} [CommRing A] [Algebra (MvPolynomial (Fin n) ℂ) A]
    [Algebra.FormallyUnramified (MvPolynomial (Fin n) ℂ) A]
    [Algebra.EssFiniteType (MvPolynomial (Fin n) ℂ) A]
    (g : A →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)
    (hg : g.comp (algebraMap (MvPolynomial (Fin n) ℂ) A) = MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x) : g.Flat :=
  flat_of_unramified_composite g (hg.symm ▸ MultivariableGermFlatness.AnalyticLocal.mvPolynomialGermMap_flat n x)

end

end OAI.AlgebraicGeometry.Comparison.Betti.UnramifiedGermFlatness.AnalyticLocal
