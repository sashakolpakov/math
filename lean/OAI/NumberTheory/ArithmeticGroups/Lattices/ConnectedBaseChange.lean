import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateQuotientBaseChange
import OAI.NumberTheory.ArithmeticGroups.Lattices.TensorDomainSpecialization

/-! # Connected Base Change -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ConnectedBaseChange.Construction

noncomputable section

section

/-! The coordinate algebra of a geometrically connected characteristic
zero matrix group is geometrically integral over every extension field. -/

open scoped Classical TensorProduct
open Set

theorem geometricVanishingIdeal_eq_baseChange_ideal
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    GeometricIrreducibility.Construction.geometricVanishingIdeal G =
      VanishingIdeal.Construction.coordinateVanishingIdeal (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))) := by
  ext p
  rw [BaseChange.Construction.mem_vanishingIdeal_iff_rational_of_algClosed]
  simp only [GeometricIrreducibility.Construction.geometricVanishingIdeal, PrimeSpectrum.mem_vanishingIdeal, forall_mem_range]
  rfl

theorem connected_coordinate_algebra_geometric_domain
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    IsDomain (AlgebraicClosure k ⊗[k] (Algebraic.CoordinatePolynomial n k ⧸ VanishingIdeal.Construction.coordinateVanishingIdeal G)) := by
  let I := VanishingIdeal.Construction.coordinateVanishingIdeal G
  have hI : (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))).IsPrime := by
    rw [← SeparableCoordinateIdeal.Construction.vanishingIdeal_algebraicClosure_baseChange G hG,
      ← geometricVanishingIdeal_eq_baseChange_ideal]
    exact GeometricIrreducibility.Construction.geometricVanishingIdeal_isPrime G hG
  let : (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))).IsPrime := hI
  exact (CoordinateQuotientBaseChange.Construction.polynomialQuotientBaseChangeEquiv (K := AlgebraicClosure k) I).toMulEquiv.isDomain

theorem connected_coordinate_algebra_baseChange_domain
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    IsDomain (K ⊗[k] (Algebraic.CoordinatePolynomial n k ⧸ VanishingIdeal.Construction.coordinateVanishingIdeal G)) := by
  let : IsDomain (AlgebraicClosure k ⊗[k] (Algebraic.CoordinatePolynomial n k ⧸ VanishingIdeal.Construction.coordinateVanishingIdeal G)) :=
    connected_coordinate_algebra_geometric_domain G hG
  exact TensorDomainSpecialization.Construction.field_tensor_domain_of_algClosure k K _

theorem connected_coordinate_ideal_baseChange_prime
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    ((VanishingIdeal.Construction.coordinateVanishingIdeal G).map (MvPolynomial.map (algebraMap k K))).IsPrime := by
  let : IsDomain (K ⊗[k] (Algebraic.CoordinatePolynomial n k ⧸ VanishingIdeal.Construction.coordinateVanishingIdeal G)) :=
    connected_coordinate_algebra_baseChange_domain G hG
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  exact MulEquiv.isDomain (K ⊗[k] (Algebraic.CoordinatePolynomial n k ⧸ VanishingIdeal.Construction.coordinateVanishingIdeal G))
    (CoordinateQuotientBaseChange.Construction.polynomialQuotientBaseChangeEquiv (K := K) (VanishingIdeal.Construction.coordinateVanishingIdeal G)).symm.toMulEquiv

end

/-! Geometric connectedness is preserved by arbitrary field extension
for the characteristic-zero matrix groups in Lattices. -/

open scoped Classical
open Set _root_.TopologicalSpace _root_.Topology

theorem irreducible_of_inducing_range
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsInducing f) (hr : IsIrreducible (range f)) : IrreducibleSpace X := by
  have hne : Nonempty X := by
    obtain ⟨_, x, _⟩ := hr.nonempty
    exact ⟨x⟩
  let : Nonempty X := hne
  have hp : IsPreirreducible (univ : Set X) := by
    intro U V hU hV hUn hVn
    obtain ⟨U', hU', rfl⟩ := hf.isOpen_iff.mp hU
    obtain ⟨V', hV', rfl⟩ := hf.isOpen_iff.mp hV
    obtain ⟨x, _, hx⟩ := hUn
    obtain ⟨y, _, hy⟩ := hVn
    obtain ⟨z, ⟨a, rfl⟩, hzU, hzV⟩ := hr.isPreirreducible U' V' hU' hV'
      ⟨f x, mem_range_self x, hx⟩ ⟨f y, mem_range_self y, hy⟩
    exact ⟨a, mem_univ a, hzU, hzV⟩
  exact { isPreirreducible_univ := hp, toNonempty := hne }

theorem connected_of_geometricVanishingIdeal_prime
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (hI : (GeometricIrreducibility.Construction.geometricVanishingIdeal G).IsPrime) : G.IsGeometricallyConnected := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  have hr : IsIrreducible (range G.geometricPrime) :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mpr hI
  let : IrreducibleSpace G.GeometricPoints := irreducible_of_inducing_range ⟨rfl⟩ hr
  change ConnectedSpace G.GeometricPoints
  infer_instance

theorem matrixGroupBaseChange_trans
    {k K L : Type} [Field k] [Field K] [Field L] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (ι : k →+* K) (ρ : K →+* L) :
    BaseChange.Construction.matrixGroupBaseChange (BaseChange.Construction.matrixGroupBaseChange G ι) ρ = BaseChange.Construction.matrixGroupBaseChange G (ρ.comp ι) := by
  unfold BaseChange.Construction.matrixGroupBaseChange
  congr 1
  rw [image_image]
  congr 1
  funext p
  exact MvPolynomial.map_map ι ρ p

theorem geometrically_connected_baseChange
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)).IsGeometricallyConnected := by
  apply connected_of_geometricVanishingIdeal_prime
  rw [geometricVanishingIdeal_eq_baseChange_ideal, matrixGroupBaseChange_trans,
    ← IsScalarTower.algebraMap_eq k K (AlgebraicClosure K), GeneralVanishingBaseChange.Construction.vanishingIdeal_charZero_baseChange G hG]
  exact connected_coordinate_ideal_baseChange_prime G hG

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ConnectedBaseChange.Construction
