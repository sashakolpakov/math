import OAI.NumberTheory.ArithmeticGroups.Lattices.ZariskiCommutator
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Solvable

/-! # Rational Geometric Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RationalGeometricEquiv.Construction

noncomputable section

section

/-! Solvable normal subgroups of the geometric points of an Lattices semisimple
matrix group are finite. -/

open scoped Classical commutatorElement
open Set _root_.TopologicalSpace

theorem semisimple_geometric_normal_solvable_finite
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (hG : G.IsSemisimple) (K : Subgroup G.GeometricPoints) [K.Normal]
    [Group.IsSolvable K] : Finite K := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let : T1Space G.GeometricPoints := ⟨ZariskiCommutator.Construction.geometric_singleton_closed G⟩
  let : SeparatelyContinuousMul G.GeometricPoints := {
    continuous_const_mul := fun {g} => Zariski.Construction.geometric_left_mul_continuous G g
    continuous_mul_const := fun {g} => Zariski.Construction.geometric_right_mul_continuous G g }
  let : ContinuousInv G.GeometricPoints := ⟨Zariski.Construction.geometric_inv_continuous G⟩
  let : NoetherianSpace G.GeometricPoints := Zariski.Construction.geometric_noetherian G
  let L := SeparateClosure.Construction.separateSubgroupClosure K
  let : L.Normal := SeparateClosure.Construction.separateSubgroupClosure_normal K
  let : Group.IsSolvable L := SeparateClosure.Construction.separateClosure_solvable
    (ZariskiCommutator.Construction.geometric_commutator_left_continuous G) (ZariskiCommutator.Construction.geometric_commutator_right_continuous G) K
  let : Finite L := Lattices.Finite.Solvable.Construction.finite_closed_normal_solvable hG L isClosed_closure
  let f : K → L := fun x => ⟨x.val, subset_closure x.property⟩
  apply Finite.of_injective f
  intro x y he
  have hv : (f x).val = (f y).val := congrArg (fun z : L => z.val) he
  exact Subtype.ext hv

theorem finite_normal_subgroup_le_center_of_connected
    {H : Type*} [Group H] [TopologicalSpace H] [T1Space H] [ConnectedSpace H]
    (hconj : ∀ x : H, Continuous (fun g : H => g * x * g⁻¹))
    (K : Subgroup H) [K.Normal] [Finite K] : K ≤ Subgroup.center H := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro g
  let f : H → K := fun h => ⟨h * x * h⁻¹,
    Subgroup.Normal.conj_mem inferInstance x hx h⟩
  have hf : Continuous f := (hconj x).subtype_mk _
  have h : f g = f 1 := PreconnectedSpace.constant (inferInstance : PreconnectedSpace H) hf
  have he : g * x * g⁻¹ = x := by
    simpa only [f, one_mul, inv_one, mul_one] using congrArg (fun z : K => z.val) h
  exact mul_inv_eq_iff_eq_mul.mp he

theorem semisimple_geometric_normal_solvable_le_center
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (hconnected : G.IsGeometricallyConnected) (hG : G.IsSemisimple)
    (K : Subgroup G.GeometricPoints) [K.Normal] [Group.IsSolvable K] :
    K ≤ Subgroup.center G.GeometricPoints := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let : T1Space G.GeometricPoints := ⟨ZariskiCommutator.Construction.geometric_singleton_closed G⟩
  let : ConnectedSpace G.GeometricPoints := hconnected
  let : Finite K := semisimple_geometric_normal_solvable_finite G hG K
  apply finite_normal_subgroup_le_center_of_connected _ K
  intro x
  have h := (Zariski.Construction.geometric_right_mul_continuous G x).comp (ZariskiCommutator.Construction.geometric_commutator_left_continuous G x)
  have he : (fun g : G.GeometricPoints => g * x * g⁻¹) =
      (fun y : G.GeometricPoints => y * x) ∘ (fun g => ⁅g, x⁆) := by
    funext g
    simp only [Function.comp_apply, commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  rw [he]
  exact h

end

/-! Over an algebraically closed base field, rational and geometric
points are isomorphic. -/

open scoped Classical

theorem matrixGroup_map_surjective
    {k K L : Type} [Field k] [Field K] [Field L] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (ι : k →+* K) (f : K →+* L)
    (hf : Function.Surjective f) : Function.Surjective (G.map ι f) := by
  let e : K ≃+* L := RingEquiv.ofBijective f ⟨f.injective, hf⟩
  intro y
  let x : Algebraic.SL n K := Matrix.SpecialLinearGroup.map e.symm.toRingHom y.val
  have he : Matrix.SpecialLinearGroup.map f x = y.val := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change e (e.symm (y.val i j)) = y.val i j
    exact e.apply_symm_apply _
  have hx : x ∈ G.subgroup K ι := by
    apply (G.mem_iff K ι x).mpr
    intro p hp
    apply f.injective
    rw [map_zero]
    have hev : f (Algebraic.evaluateMatrix ι x p) =
        Algebraic.evaluateMatrix (f.comp ι) (Matrix.SpecialLinearGroup.map f x) p := by
      simp only [Algebraic.evaluateMatrix, MvPolynomial.map_eval₂Hom,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [hev, he]
    exact (G.mem_iff L (f.comp ι) y.val).mp y.property p hp
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

def rationalGeometricEquiv {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : G.RationalPoints ≃* G.GeometricPoints :=
  MulEquiv.ofBijective (G.map (RingHom.id k) (algebraMap k (AlgebraicClosure k)))
    ⟨G.map_injective _ _, matrixGroup_map_surjective G _ _
      IsAlgClosed.algebraMap_bijective_of_isIntegral.surjective⟩

theorem semisimple_algClosed_normal_solvable_finite
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsSemisimple)
    (K : Subgroup G.RationalPoints) [K.Normal] [Group.IsSolvable K] : Finite K := by
  let e := rationalGeometricEquiv G
  let N := K.map e.toMonoidHom
  let : N.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let : Group.IsSolvable N := Group.isSolvable_of_surjective
    (f := e.toMonoidHom.subgroupMap K) (MonoidHom.subgroupMap_surjective _ _)
  let : Finite N := semisimple_geometric_normal_solvable_finite G hG N
  exact Finite.of_injective (e.toMonoidHom.subgroupMap K)
    (fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RationalGeometricEquiv.Construction
