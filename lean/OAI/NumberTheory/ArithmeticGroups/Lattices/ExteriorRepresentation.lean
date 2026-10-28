import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.ExteriorVector
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices

/-! # Exterior Representation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorRepresentation.Construction

noncomputable section

/-! Exterior powers as group representations, with the integral lattice
preserved by the standard arithmetic subgroup. -/

open scoped Classical _root_.NumberField

def exteriorLinearEquiv {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (r : ℕ) (f : V ≃ₗ[k] V) : (⋀[k]^r V) ≃ₗ[k] (⋀[k]^r V) :=
  LinearEquiv.ofLinearMap (exteriorPower.map r f.toLinearMap)
    (exteriorPower.map r f.symm.toLinearMap)
    (by
      rw [← exteriorPower.map_comp]
      have he : f.toLinearMap.comp f.symm.toLinearMap = LinearMap.id := by ext x; simp
      rw [he, exteriorPower.map_id])
    (by
      rw [← exteriorPower.map_comp]
      have he : f.symm.toLinearMap.comp f.toLinearMap = LinearMap.id := by ext x; simp
      rw [he, exteriorPower.map_id])

def exteriorRepresentation {k V H : Type*} [Field k] [AddCommGroup V] [Module k V] [Group H]
    (r : ℕ) (ρ : H →* (V ≃ₗ[k] V)) : H →* ((⋀[k]^r V) ≃ₗ[k] (⋀[k]^r V)) where
  toFun g := exteriorLinearEquiv r (ρ g)
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    change exteriorPower.map r (ρ 1).toLinearMap = LinearMap.id
    rw [map_one]
    exact exteriorPower.map_id
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    change exteriorPower.map r (ρ (g * h)).toLinearMap =
      (exteriorPower.map r (ρ g).toLinearMap).comp (exteriorPower.map r (ρ h).toLinearMap)
    rw [map_mul]
    exact exteriorPower.map_comp (ρ h).toLinearMap (ρ g).toLinearMap

def boundedExteriorRepresentation {k : Type} [Field k] {n : ℕ} (d r : ℕ) :
    Algebraic.SL n k →* ((⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)) ≃ₗ[k] (⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d))) :=
  exteriorRepresentation r (BoundedRepresentation.Construction.boundedPolynomialRepresentation d)

theorem standard_arithmetic_exterior_lattice_stable
    {k : Type} [Field k] [NumberField k] {n d r : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) {g : G.RationalPoints}
    (hg : g ∈ G.latticeStabilizer (IntegralLattice.FullLattice.standard k n))
    {w : ⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)}
    (hw : w ∈ ExteriorLattice.Construction.exteriorLatticeSpan (k := k)
      (Integral.Polynomial.Construction.boundedIntegralPolynomialLattice (R := 𝓞 k) (k := k) n d) r) :
    boundedExteriorRepresentation d r g.val w ∈ ExteriorLattice.Construction.exteriorLatticeSpan (k := k)
      (Integral.Polynomial.Construction.boundedIntegralPolynomialLattice (R := 𝓞 k) (k := k) n d) r := by
  obtain ⟨A, hA⟩ := (Integral.Matrices.Construction.standard_lattice_stabilizer_iff_integral G g).mp hg
  rw [← hA]
  exact Integral.ExteriorVector.Construction.integral_exterior_lattice_action_mem A hw

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorRepresentation.Construction
