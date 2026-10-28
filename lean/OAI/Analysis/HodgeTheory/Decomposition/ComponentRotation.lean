import OAI.Analysis.HodgeTheory.Decomposition.InfinitesimalTypeEigen

/-! # Component Rotation -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComponentRotation.Constructions

noncomputable section

section

/-! The smooth type decomposition identifies the componentwise rotation
operator with a diagonal operator having distinct genuine bidegrees. -/

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)

theorem componentProjection_on_pure (i j : Core.Constructions.Bidegree n) (a : X.componentForms n)
    (ha : a ∈ Core.Constructions.pureFormsAt X n j) : Projectors.Constructions.componentProjection X n i a = if i = j then a else 0 := by
  have he : ∀ z, Types.Constructions.componentAction X n z a = Types.Constructions.inverseTypeCharacter j z • a := by
    rw [Types.Constructions.pureFormsAt_eq_eigenspaces] at ha
    simpa only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] using ha
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact Projectors.Constructions.spectralProjector_identity _ _ (Types.Constructions.inverseTypeCharacter_injective n) i a he
  · rw [ite_eq_right hij]
    exact Projectors.Constructions.spectralProjector_zero _ _ (Types.Constructions.inverseTypeCharacter_injective n) i j hij a he

def componentRotation : Module.End ℂ (X.componentForms n) :=
  ∑ i : Core.Constructions.Bidegree n, InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue i • Projectors.Constructions.componentProjection X n i

theorem componentRotation_apply (a : X.componentForms n) :
    componentRotation X n a = ∑ i : Core.Constructions.Bidegree n, InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue i • Projectors.Constructions.componentProjection X n i a := by
  simp only [componentRotation, LinearMap.sum_apply, LinearMap.smul_apply]

theorem componentRotation_pure (i : Core.Constructions.Bidegree n) (a : X.componentForms n)
    (ha : a ∈ Core.Constructions.pureFormsAt X n i) : componentRotation X n a = InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue i • a := by
  rw [componentRotation_apply]
  simp_rw [componentProjection_on_pure X n _ i a ha]
  simp

theorem componentProjection_rotation (i : Core.Constructions.Bidegree n) (a : X.componentForms n) :
    Projectors.Constructions.componentProjection X n i (componentRotation X n a) =
      InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue i • Projectors.Constructions.componentProjection X n i a := by
  rw [componentRotation_apply, map_sum]
  simp_rw [map_smul, componentProjection_on_pure X n i _ _ (Projectors.Constructions.componentProjection_pure X n _ a)]
  simp

theorem componentRotation_eigen_iff (i : Core.Constructions.Bidegree n) (a : X.componentForms n) :
    componentRotation X n a = InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue i • a ↔ a ∈ Core.Constructions.pureFormsAt X n i := by
  refine ⟨fun h => ?_, componentRotation_pure X n i a⟩
  have hz (j : Core.Constructions.Bidegree n) (hji : j ≠ i) : Projectors.Constructions.componentProjection X n j a = 0 := by
    have hj := congrArg (Projectors.Constructions.componentProjection X n j) h
    rw [componentProjection_rotation, map_smul] at hj
    have hs : (InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue j - InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue i) • Projectors.Constructions.componentProjection X n j a = 0 := by
      rw [sub_smul, hj, sub_self]
    exact (smul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr (fun he => hji (InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue_injective n he)))
  have he : a = Projectors.Constructions.componentProjection X n i a := by
    conv_lhs => rw [← Projectors.Constructions.sum_componentProjection X n a]
    exact Finset.sum_eq_single i (fun j _ hji => hz j hji) (fun hi => (hi (Finset.mem_univ i)).elim)
  rw [he]
  exact Projectors.Constructions.componentProjection_pure X n i a

theorem componentOperator_preserves_type_of_rotation (T : Module.End ℂ (X.componentForms n))
    (hT : ∀ a, componentRotation X n (T a) = T (componentRotation X n a))
    (i : Core.Constructions.Bidegree n) (a : X.componentForms n) (ha : a ∈ Core.Constructions.pureFormsAt X n i) :
    T a ∈ Core.Constructions.pureFormsAt X n i := by
  apply (componentRotation_eigen_iff X n i (T a)).mp
  rw [hT, componentRotation_pure X n i a ha, map_smul]

end

/-! An actual complex-linear operator preserving each smooth bidegree
commutes with every already constructed type projector. -/

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)

theorem componentOperator_projection (T : Module.End ℂ (X.componentForms n))
    (hT : ∀ i a, a ∈ Core.Constructions.pureFormsAt X n i → T a ∈ Core.Constructions.pureFormsAt X n i)
    (i : Core.Constructions.Bidegree n) (a : X.componentForms n) :
    Projectors.Constructions.componentProjection X n i (T a) = T (Projectors.Constructions.componentProjection X n i a) := by
  have hsum := congrArg T (Projectors.Constructions.sum_componentProjection X n a)
  rw [map_sum] at hsum
  calc
    _ = Projectors.Constructions.componentProjection X n i (∑ j : Core.Constructions.Bidegree n, T (Projectors.Constructions.componentProjection X n j a)) := congrArg _ hsum.symm
    _ = ∑ j : Core.Constructions.Bidegree n, Projectors.Constructions.componentProjection X n i (T (Projectors.Constructions.componentProjection X n j a)) := map_sum _ _ _
    _ = T (Projectors.Constructions.componentProjection X n i a) := by
      simp_rw [componentProjection_on_pure X n i _ _ (hT _ _ (Projectors.Constructions.componentProjection_pure X n _ a))]
      simp

end

end OAI.Analysis.HodgeTheory.Decomposition.ComponentRotation.Constructions
