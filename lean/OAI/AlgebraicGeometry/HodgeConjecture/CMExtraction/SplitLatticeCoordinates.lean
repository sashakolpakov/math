import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeProduct
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeGenerators
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarRangeCoordinates

/-! # Split Lattice Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeCoordinates.TestTransport

noncomputable section

/-! In the retained integral basis, the split completion of the
original lattice is precisely the p-adically integral coordinate vectors. -/

open scoped Classical

open _root_.Module

variable (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
  (q : ℕ) [Fact q.Prime] [Algebra E (Padic q)] [IsScalarTower ℚ E (Padic q)]
  {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (σ : S ≃ (E →ₐ[ℚ] Padic q))
  (L : Submodule ℤ (Fin 3 → E)) [Submodule.IsLattice ℚ L] (b : Basis J ℤ L)

omit [Fintype S] [DecidableEq S] in
theorem splitLabelCoordinates_lattice_basis (j : J) :
    SplitCoordinates.TestTransport.splitLabelCoordinates E (Padic q) σ (b.extendOfIsLattice ℚ).equivFun
      (fun v i => σ v ((b j).val i)) = Pi.single j 1 := by
  rw [SplitCoordinates.TestTransport.splitLabelCoordinates_rational]
  funext k
  have h := (b.extendOfIsLattice ℚ).equivFun_self j k
  rw [Basis.extendOfIsLattice_apply] at h
  rw [h]
  by_cases hjk : j = k
  · subst k
    simp
  · simp [hjk, Ne.symm hjk]

omit [Fintype S] [DecidableEq S] in
theorem splitLatticeImage_padic_coordinates (x : S → Fin 3 → Padic q) :
    x ∈ SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (fun v => (σ v).toRingHom) L ↔
      ∀ j, ‖SplitCoordinates.TestTransport.splitLabelCoordinates E (Padic q) σ (b.extendOfIsLattice ℚ).equivFun x j‖ ≤ 1 := by
  let f : (Fin 3 → E) →+ (S → Fin 3 → Padic q) :=
    AddMonoidHom.pi (fun v => AddMonoidHom.pi (fun i =>
      (σ v).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin 3 => E) i)))
  have hspan : Submodule.span (PadicInt q) (Set.range (fun j => f (b j).val)) =
      SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (fun v => (σ v).toRingHom) L :=
    LatticeGenerators.TestTransport.span_image_integral_basis (A := PadicInt q) L b f
  rw [← hspan, ScalarRangeCoordinates.TestTransport.span_basis_scalar_coordinates
    (SplitCoordinates.TestTransport.splitLabelCoordinates E (Padic q) σ (b.extendOfIsLattice ℚ).equivFun) (fun j => f (b j).val)
    (splitLabelCoordinates_lattice_basis E q σ L b)]
  apply forall_congr'
  intro j
  constructor
  · rintro ⟨r, hr⟩
    exact hr ▸ r.property
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeCoordinates.TestTransport
