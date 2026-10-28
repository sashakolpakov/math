import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.OrderStabilizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.EuclideanBracketRealization

/-! # Killing Order Stabilizer Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.KillingOrderStabilizerLattice.Construction

noncomputable section

/-! The integral order stabilizer of a real Killing Lie algebra is a lattice. -/

theorem killing_order_stabilizer_isLattice
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (Λ : Submodule ℤ L) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, B x y ∈ Λ) : IntegralLattice.IsLattice (Bracket.OrderStabilizer.Construction.bracketOrderStabilizer B Λ) := by
  obtain ⟨m, e, hmap, hcoeff⟩ := Integral.EuclideanBracketRealization.Construction.integral_lattice_bilinear_euclidean_coordinates Λ B hint
  let C := Positive.Killing.Construction.continuousBracketTransport e B
  have hC := Positive.Killing.Construction.continuousBracketTransport_isLie e B hB
  have hCK := Positive.Killing.Construction.continuousBracketTransport_killing_nondegenerate e B hK
  have hl := Integral.BracketLattice.Construction.integralBracketSubgroup_isLattice (EuclideanSpace.basisFun (Fin m) ℝ) C hC hCK hcoeff
  rw [Bracket.OrderStabilizer.Construction.integralBracketSubgroup_eq_orderStabilizer, ← hmap] at hl
  let E := Bracket.TransportGroupEquiv.Construction.bracketTransportGroupEquiv e B
  let f := E.toMonoidHom
  let : Subsingleton f.ker := ⟨fun x y => Subtype.ext (E.injective (x.property.trans y.property.symm))⟩
  let : Finite f.ker := inferInstance
  have ht := LatticeEquivTransport.Construction.lattice_comap_of_open_surjective_finite_kernel f E.surjective E.continuous E.isOpenMap _ hl
  rwa [Bracket.OrderStabilizer.Construction.bracketOrderStabilizer_transport] at ht

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.KillingOrderStabilizerLattice.Construction
