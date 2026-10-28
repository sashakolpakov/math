import OAI.AlgebraicGeometry.Resolution.Blowups.JacobianDerivationFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleFrame

/-! # Transverse Finite Frame Correction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransverseFiniteFrameCorrection.Construction

noncomputable section

/-! A finite tangent frame can be normalized while retaining an existing normal equation. -/

variable {k R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem derivation_sum_smul_apply (D : ι → Derivation k R R) (a : ι → R) (x : R) :
    (∑ i, a i • D i) x = ∑ i, a i * D i x := by
  have h := congrArg (fun f : R → R => f x)
    (map_sum (Derivation.coeFnAddMonoidHom : Derivation k R R →+ R → R)
      (fun i => a i • D i) Finset.univ)
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply, Derivation.smul_apply, smul_eq_mul] using h

theorem normalizedJacobianFrame_annihilates (E : ι → Derivation k R R) (g : ι → R)
    (z : R) (hz : ∀ i, E i z = 0) (i : ι) : JacobianDerivationFrame.Construction.normalizedJacobianFrame E g i z = 0 := by
  rw [JacobianDerivationFrame.Construction.normalizedJacobianFrame_apply]
  simp only [hz, mul_zero, Finset.sum_const_zero]

theorem exists_normal_derivation_annihilating_frame
    (D : Derivation k R R) (E : ι → Derivation k R R) (g : ι → R) (z : R)
    (hDz : D z = 1) (hEz : ∀ i, E i z = 0)
    (hEg : ∀ i j, E i (g j) = if i = j then 1 else 0) :
    ∃ F : Derivation k R R, F z = 1 ∧ ∀ i, F (g i) = 0 := by
  refine ⟨D - ∑ i, D (g i) • E i, ?_, ?_⟩
  · rw [Derivation.sub_apply, derivation_sum_smul_apply]
    simp only [hDz, hEz, mul_zero, Finset.sum_const_zero, sub_zero]
  · intro j
    rw [Derivation.sub_apply, derivation_sum_smul_apply]
    simp only [hEg, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]

omit [Fintype ι] [DecidableEq ι] in
theorem transverseExtendedCoordinates_span (g : ι → R) (z : R) :
    Ideal.span (Set.range (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g z)) = Ideal.span (Set.range g) ⊔ Ideal.span {z} := by
  have he : Set.range (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g z) = Set.range g ∪ {z} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      cases a with
      | none => exact Or.inr rfl
      | some i => exact Or.inl ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨some i, rfl⟩
      · exact ⟨none, rfl⟩
  rw [he, Ideal.span_union]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransverseFiniteFrameCorrection.Construction
