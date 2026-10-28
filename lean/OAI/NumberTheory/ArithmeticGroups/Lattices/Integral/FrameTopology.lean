import OAI.NumberTheory.ArithmeticGroups.Lattices.RealSpecialLinearCoordinates

/-! # Frame Topology -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.FrameTopology.Construction

noncomputable section

/-! A real frame consisting of lattice vectors detects the topology of
its integral matrix stabilizer. -/

open scoped Classical
open _root_.Module

theorem special_frame_stabilizer_discrete_of_integral_frame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} (Λ : Submodule ℤ E) [DiscreteTopology Λ] (b : Basis (Fin m) ℝ E)
    (hb : ∀ i, b i ∈ Λ) :
    DiscreteTopology ((SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ).comap
      Matrix.SpecialLinearGroup.toGL) := by
  let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ).comap Matrix.SpecialLinearGroup.toGL
  let f : Γ → (Fin m → Λ) := fun g i => ⟨RealSpecialLinearCoordinates.Construction.specialFrameRepresentation b g.val (b i),
    ((StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ g.val.toGL).mp
      g.property (b i)).mpr (hb i)⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro i
    exact ((RealSpecialLinearCoordinates.Construction.continuous_specialFrameRepresentation b).comp
      (continuous_subtype_val.prodMk continuous_const)).subtype_mk _
  · intro g h he
    apply Subtype.ext
    apply RealSpecialLinearCoordinates.Construction.specialFrameRepresentation_injective b
    apply b.ext'
    intro i
    exact congrArg (fun z : Fin m → Λ => (z i).val) he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.FrameTopology.Construction
