import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupFunctionField

/-! # Open Chart Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenChartDimension.Construction

noncomputable section

/-! Differential dimension in any affine open chart of an abelian fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem finrank_fractionField_differentials_of_open_chart
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (B : Type u) [CommRing B] [IsDomain B] [Algebra k B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra k L] [IsScalarTower k B L]
    (j : Spec (.of B) ⟶ A.left) [IsOpenImmersion j]
    (hj : j ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap k B))) :
    (Module.finrank L (KaehlerDifferential k L) : WithBot ℕ∞) =
      topologicalKrullDim A.left := by
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
    rw [← hj]
    infer_instance
  have : Algebra.Smooth k B := by
    exact (RingHom.smooth_algebraMap).mp
      ((HasRingHomProperty.Spec_iff (P := @Smooth)
        (φ := CommRingCat.ofHom (algebraMap k B))).mp inferInstance)
  have : JacobsonSpace (Spec (.of B)) :=
    LocallyOfFiniteType.jacobsonSpace (Spec.map (CommRingCat.ofHom (algebraMap k B)))
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  obtain ⟨q, _, hq⟩ := nonempty_inter_closedPoints
    (X := Spec (.of B)) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have : q.asIdeal.IsMaximal := q.isClosed_singleton_iff_isMaximal.mp hq
  have hjq : IsClosed {j q} := by
    change q ∈ j ⁻¹' closedPoints A.left
    rw [j.isOpenEmbedding.preimage_closedPoints]
    exact hq
  have hdim : topologicalKrullDim A.left = ringKrullDim (Localization.AtPrime q.asIdeal) := by
    rw [GroupDimension.Construction.topologicalKrullDim_eq_stalk_of_transitive_closedPoints A.left (fun x y hx hy => by
      obtain ⟨α, _, hxy, _⟩ := FlatTranslations.Construction.multiplication_transitive_automorphisms A 1 x y hx hy
      exact ⟨α, hxy⟩) (j q) hjq,
      ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion j,
      ← ringKrullDim_stalk_eq_coheight]
    exact ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of B) q).commRingCatIsoToRingEquiv
  exact (FunctionFieldDifferentials.Construction.finrank_fractionField_kaehler_eq_local_dimension k B L q.asIdeal).trans hdim.symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenChartDimension.Construction
