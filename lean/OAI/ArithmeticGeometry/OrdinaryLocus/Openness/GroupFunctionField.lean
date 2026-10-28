import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FunctionFieldDifferentials
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension

/-! # Group Function Field -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupFunctionField.Construction

noncomputable section

/-! Function-field differential dimension of the abelian fibers in Openness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The base-field action on the coordinate ring of an affine chart. -/
abbrev chartAlgebra
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (U : X.Opens) (hU : IsAffineOpen U) : Algebra K Γ(X, U) :=
  (Spec.preimage (hU.fromSpec ≫ f)).hom.toAlgebra

/-- The function field of any nonempty affine chart of a smooth proper
connected algebraic group has differential dimension equal to the group dimension. -/
theorem finrank_chart_fractionField_differentials
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (U : A.left.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := chartAlgebra A.hom U hU
    (Module.finrank (FractionRing Γ(A.left, U))
      (KaehlerDifferential K (FractionRing Γ(A.left, U))) : WithBot ℕ∞) =
      topologicalKrullDim A.left := by
  let := chartAlgebra A.hom U hU
  have : IsIntegral A.left := ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A
  let B := Γ(A.left, U)
  let Q := FractionRing B
  let φ := Spec.preimage (hU.fromSpec ≫ A.hom)
  let : Algebra K B := φ.hom.toAlgebra
  have : IsScalarTower K B Q := inferInstance
  have : Smooth (Spec.map φ) := by
    dsimp [φ]
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.Smooth K B :=
    (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := φ)).mp inferInstance
  have : JacobsonSpace (Spec (.of B)) := LocallyOfFiniteType.jacobsonSpace (Spec.map φ)
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  obtain ⟨p, _, hp⟩ := nonempty_inter_closedPoints
    (X := Spec (.of B)) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have : p.asIdeal.IsMaximal := p.isClosed_singleton_iff_isMaximal.mp hp
  have hx : IsClosed {hU.fromSpec p} := by
    change p ∈ hU.fromSpec ⁻¹' closedPoints A.left
    rw [hU.fromSpec.isOpenEmbedding.preimage_closedPoints]
    exact hp
  have hdim : topologicalKrullDim A.left = ringKrullDim (Localization.AtPrime p.asIdeal) := by
    rw [GroupDimension.Construction.topologicalKrullDim_eq_stalk_of_transitive_closedPoints A.left (fun x y hx hy => by
      obtain ⟨α, _, hxy, _⟩ := FlatTranslations.Construction.multiplication_transitive_automorphisms A 1 x y hx hy
      exact ⟨α, hxy⟩) (hU.fromSpec p) hx,
      ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion hU.fromSpec,
      ← ringKrullDim_stalk_eq_coheight]
    exact ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of B) p).commRingCatIsoToRingEquiv
  exact (FunctionFieldDifferentials.Construction.finrank_fractionField_kaehler_eq_local_dimension K B Q p.asIdeal).trans hdim.symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupFunctionField.Construction
