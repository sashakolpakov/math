import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FrobeniusAdapter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Interfaces

/-! # Shared -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The complete repaired IntegralComparison proposition, with native polynomial transport at the split prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.NumberTheory.PadicHodge.IntegralComparison.Interfaces

universe u

/-- The full native characteristic-polynomial comparison proposition as an explicit input. -/
def Integral.Shared.CharpolyInput : Prop :=
  ∀
    (p ℓ a : ℕ)
    [Fact p.Prime] [Fact ℓ.Prime]
    (_hℓp : ℓ ≠ p)
    (_ha : 0 < a)
    (k : Type u) [Field k] [Fintype k] [CharP k p]
    (hcard : Fintype.card k = p ^ a)
    (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] [IsProper f]
    (_hprojective : IntegralComparison.Interfaces.ProjectiveOver f)
    (i : ℕ),
    ∃ (hcrys : FiniteDimensional (FractionRing (WittVector p k)) (IntegralComparison.Interfaces.CrystallineCohomology p k f i))
      (het : FiniteDimensional ℚ_[ℓ] (IntegralComparison.Interfaces.EtaleCohomology ℓ k f i)),
      letI := hcrys
      letI := het
      ∃ P : Polynomial ℤ,
        LinearMap.charpoly (IntegralComparison.Interfaces.crystallineQFrobenius p a k hcard f i) =
          P.map (Int.castRingHom (FractionRing (WittVector p k))) ∧
        LinearMap.charpoly (IntegralComparison.Interfaces.etaleGeometricFrobenius ℓ p a k hcard f i) =
          P.map (Int.castRingHom ℚ_[ℓ])

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

/-- IntegralComparison supplies the shared integral polynomial once projectivity of the actual special fiber is proved. -/
theorem Geometry.AbelianH1Model.sharedPolynomial_of_IntegralComparison (hIntegralComparison : Integral.Shared.CharpolyInput.{0})
    (hprojective : IntegralComparison.Interfaces.ProjectiveOver A.specialFiber.scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
      letI := hC
      ∃ P : Polynomial ℤ, A.IsWeilPolynomial ℓ P ∧
        A.crystallineFrobenius.charpoly = P.map (Int.castRingHom ℚ_[q]) := by
  obtain ⟨hsmall, het, P, hP, hEt⟩ := hIntegralComparison q ℓ 1 hℓq (by decide) (ZMod q)
    (by simp) A.specialFiber.scheme.left A.specialFiber.scheme.hom hprojective 1
  let : FiniteDimensional (FractionRing (GeometricComparison.Crystalline.CoefficientAdapter.Witt q))
      (IntegralComparison.Interfaces.CrystallineCohomology q (ZMod q) A.specialFiber.scheme.hom 1) := hsmall
  let e : IntegralComparison.Interfaces.CrystallineCohomology q (ZMod q) A.specialFiber.scheme.hom 1
      ≃ₛₗ[(GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q).toRingHom] A.Crystalline :=
    Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv q A.specialFiber.scheme
  let T := IntegralComparison.Interfaces.crystallineQFrobenius q 1 (ZMod q) (by simp) A.specialFiber.scheme.hom 1
  have he : ∀ x, e (T x) = A.crystallineFrobenius (e x) :=
    Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv_frobenius q A.specialFiber.scheme
  let hC : FiniteDimensional ℚ_[q] A.Crystalline :=
    SemilinearCharpolyTo.SemilinearCharpoly.finite (GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q) e
  refine ⟨hC, P, ⟨het, hEt⟩, ?_⟩
  rw [SemilinearCharpolyTo.SemilinearCharpoly.charpoly_map (GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q) e T
    A.crystallineFrobenius he, hP, Polynomial.map_map]
  congr 1
  exact Subsingleton.elim _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
