import OAI.NumberTheory.ArithmeticGroups.Lattices.Zariski
import OAI.NumberTheory.ArithmeticGroups.Lattices.IrreducibleGroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIdeal

/-! # Geometric Irreducibility -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricIrreducibility.Construction

noncomputable section

section

/-! Irreducibility and the geometric prime ideal of a connected matrix group. -/

open _root_.TopologicalSpace Set

theorem geometrically_connected_irreducible
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (hG : G.IsGeometricallyConnected) :
    @IrreducibleSpace G.GeometricPoints G.geometricTopology := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let : SeparatelyContinuousMul G.GeometricPoints := {
    continuous_const_mul := fun {g} => Zariski.Construction.geometric_left_mul_continuous G g
    continuous_mul_const := fun {g} => Zariski.Construction.geometric_right_mul_continuous G g }
  let : ContinuousInv G.GeometricPoints := ⟨Zariski.Construction.geometric_inv_continuous G⟩
  let : NoetherianSpace G.GeometricPoints := Zariski.Construction.geometric_noetherian G
  let : ConnectedSpace G.GeometricPoints := hG
  exact IrreducibleGroup.Construction.irreducible_of_connected_noetherian_group G.GeometricPoints

def geometricVanishingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : Ideal (Algebraic.CoordinatePolynomial n (AlgebraicClosure k)) :=
  PrimeSpectrum.vanishingIdeal (range G.geometricPrime)

theorem geometricVanishingIdeal_isPrime
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (hG : G.IsGeometricallyConnected) : (geometricVanishingIdeal G).IsPrime := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let : IrreducibleSpace G.GeometricPoints := geometrically_connected_irreducible G hG
  apply PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ G.GeometricPoints).image G.geometricPrime
      (Zariski.Construction.continuous_geometricPrime G).continuousOn

theorem geometricVanishingIdeal_comap {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) :
    (geometricVanishingIdeal G).comap (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) =
      VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  ext p
  rw [Ideal.mem_comap, CoordinateIdeal.Construction.mem_vanishingIdeal_iff_geometric]
  simp only [geometricVanishingIdeal, PrimeSpectrum.mem_vanishingIdeal, forall_mem_range]
  change (∀ x : G.GeometricPoints,
    Algebraic.evaluateMatrix (RingHom.id _) x.val (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) p) = 0) ↔ _
  simp only [Algebraic.evaluateMatrix, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

theorem coordinateVanishingIdeal_isPrime {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    (VanishingIdeal.Construction.coordinateVanishingIdeal G).IsPrime := by
  let : (geometricVanishingIdeal G).IsPrime := geometricVanishingIdeal_isPrime G hG
  rw [← geometricVanishingIdeal_comap G]
  infer_instance

end

/-! Reducedness after a separable algebraic field extension, used for
extension of coordinate ideals. -/

open scoped Classical TensorProduct

theorem domain_tensor_separable_reduced_of_essFiniteType
    (k K A : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    [Algebra.EssFiniteType k K]
    [CommRing A] [IsDomain A] [Algebra k A] : IsReduced (A ⊗[k] K) := by
  let F := FractionRing A
  let : Algebra.FormallyUnramified k K := Algebra.FormallyUnramified.of_isSeparable k K
  let : IsReduced (F ⊗[k] K) := Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[k] K)
  let f : A →ₐ[k] F := IsScalarTower.toAlgHom k A F
  have hf : Function.Injective f := IsFractionRing.injective A F
  exact isReduced_of_injective (Algebra.TensorProduct.map f 1)
    (Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf)

theorem domain_tensor_separable_reduced
    (k K A : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    [CommRing A] [IsDomain A] [Algebra k A] : IsReduced (A ⊗[k] K) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  let : Algebra.IsSeparable k B := Subalgebra.isSeparable_iff.mpr
    (fun x _ => Algebra.IsSeparable.isSeparable k x)
  let B' := Algebra.IsAlgebraic.toIntermediateField B
  let e : B ≃ₐ[k] B' :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let : Algebra.FiniteType k B' := (B.fg_iff_finiteType.mp hB).equiv e
  let : Algebra.IsSeparable k B' :=
    ⟨fun x => (isSeparable_map_iff B'.val Subtype.val_injective).mp
      (Algebra.IsSeparable.isSeparable k x.val)⟩
  let : IsReduced (A ⊗[k] B') := domain_tensor_separable_reduced_of_essFiniteType k B' A
  let E := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) e
  exact isReduced_of_injective E E.injective

theorem separable_tensor_domain_reduced
    (k K A : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    [CommRing A] [IsDomain A] [Algebra k A] : IsReduced (K ⊗[k] A) := by
  let : IsReduced (A ⊗[k] K) := domain_tensor_separable_reduced k K A
  exact isReduced_of_injective (Algebra.TensorProduct.comm k K A)
    (Algebra.TensorProduct.comm k K A).injective

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricIrreducibility.Construction
