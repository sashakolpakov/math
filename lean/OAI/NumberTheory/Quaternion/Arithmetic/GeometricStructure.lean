import OAI.NumberTheory.Quaternion.Arithmetic.GeometricConnected
import OAI.NumberTheory.Quaternion.Arithmetic.PerfectCentralQuotient
import OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicHypotheses
import OAI.NumberTheory.ArithmeticGroups.Lattices.ZariskiCommutator

/-! # Geometric Structure -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GeometricStructure

noncomputable section

/-! Geometric almost simplicity and semisimplicity of nondegenerate
quaternion norm-one matrix groups, proved through their split SL₂ form. -/

open scoped Classical IsMulCommutative
open OAI.NumberTheory.ArithmeticGroups.Lattices.ZariskiCommutator.Construction Set

variable {F : Type} [Field F] [CharZero F]

theorem quaternion_exists_geometric_specialLinearEquiv (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty ((MatrixGroup.quaternionNormOneMatrixGroup a b).GeometricPoints ≃*
      Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) := by
  let ρ := algebraMap F (AlgebraicClosure F)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (ρ b) (by decide : 0 < 2)
  have hs : x ^ 2 - ρ a * (0 : AlgebraicClosure F) ^ 2 = ρ b := by simpa using hx
  exact ⟨(MatrixGroup.quaternionMatrixPointsEquiv a b ρ).symm.trans
    (SplitGroup.quaternionNormOneSpecialLinearEquiv (ρ a) (ρ b) x 0 ((map_ne_zero ρ).mpr ha)
      ((map_ne_zero ρ).mpr hb) hs)⟩

theorem quaternion_geometric_normal_finite_or_top (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (N : Subgroup (MatrixGroup.quaternionNormOneMatrixGroup a b).GeometricPoints) [N.Normal] :
    Finite N ∨ N = ⊤ := by
  obtain ⟨e⟩ := quaternion_exists_geometric_specialLinearEquiv a b ha hb
  let : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  rcases PerfectCentralQuotient.specialLinearTwo_normal_finite_or_top (N.map e.toMonoidHom) with hf | ht
  · let : Finite (N.map e.toMonoidHom) := hf
    let ψ : N → N.map e.toMonoidHom := fun q => ⟨e q.val, ⟨q.val, q.property, rfl⟩⟩
    exact Or.inl (Finite.of_injective ψ (fun p q h =>
      Subtype.ext (e.injective (congrArg Subtype.val h))))
  · right
    have he := congrArg (Subgroup.comap e.toMonoidHom) ht
    rw [Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.comap_top] at he
    exact he

theorem quaternion_geometric_not_solvable (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ Group.IsSolvable (MatrixGroup.quaternionNormOneMatrixGroup a b).GeometricPoints := by
  intro hs
  let := hs
  obtain ⟨e⟩ := quaternion_exists_geometric_specialLinearEquiv a b ha hb
  exact PerfectCentralQuotient.specialLinearTwo_not_solvable (K := AlgebraicClosure F)
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

omit [CharZero F] in
theorem finite_connected_geometric_subgroup_eq_bot {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (N : Subgroup G.GeometricPoints) [Finite N]
    (hc : @IsConnected G.GeometricPoints G.geometricTopology (N : Set G.GeometricPoints)) : N = ⊥ := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let : T1Space G.GeometricPoints := ⟨ArithmeticGroups.Lattices.ZariskiCommutator.Construction.geometric_singleton_closed G⟩
  let : ConnectedSpace N := isConnected_iff_connectedSpace.mp hc
  let : Subsingleton N := subsingleton_of_preconnected_totallyDisconnected
  exact N.eq_bot_of_subsingleton

theorem quaternionNormOneMatrixGroup_absolutelyAlmostSimple (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    AlgebraicHypotheses.IsAbsolutelyAlmostSimple (MatrixGroup.quaternionNormOneMatrixGroup a b) := by
  let G := MatrixGroup.quaternionNormOneMatrixGroup a b
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  refine ⟨GeometricConnected.quaternionNormOneMatrixGroup_connected a b ha hb, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    let : IsMulCommutative G.GeometricPoints := IsMulCommutative.of_comm hc
    exact quaternion_geometric_not_solvable a b ha hb inferInstance
  · intro N hn _ hc
    let := hn
    rcases quaternion_geometric_normal_finite_or_top a b ha hb N with hf | ht
    · let := hf
      exact Or.inl (finite_connected_geometric_subgroup_eq_bot G N hc)
    · exact Or.inr ht

theorem quaternionNormOneMatrixGroup_semisimple (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (MatrixGroup.quaternionNormOneMatrixGroup a b).IsSemisimple := by
  let G := MatrixGroup.quaternionNormOneMatrixGroup a b
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  intro N hn _ hc hs
  let := hn
  rcases quaternion_geometric_normal_finite_or_top a b ha hb N with hf | ht
  · let := hf
    exact finite_connected_geometric_subgroup_eq_bot G N hc
  · have htop : Group.IsSolvable (⊤ : Subgroup G.GeometricPoints) := ht ▸ hs
    let := htop
    let eTop : (⊤ : Subgroup G.GeometricPoints) ≃* G.GeometricPoints := Subgroup.topEquiv
    have hsG : Group.IsSolvable G.GeometricPoints :=
      Group.isSolvable_of_surjective (f := eTop.toMonoidHom) eTop.surjective
    exact (quaternion_geometric_not_solvable a b ha hb hsG).elim

end

end OAI.NumberTheory.Quaternion.Arithmetic.GeometricStructure
