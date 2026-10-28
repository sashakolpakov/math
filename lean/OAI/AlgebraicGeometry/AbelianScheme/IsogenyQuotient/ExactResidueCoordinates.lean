import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCoordinates

/-! # Exact Residue Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ExactResidueCoordinates.Construction

noncomputable section

/-!
Residue coordinates for a surjective linear map whose kernel is the
uniformly scaled integral lattice. The coordinate formula retains the
original linear map, and is used below for restricted Tate evaluation.
-/

variable (q : ℕ) [Fact q.Prime] {d : ℕ}
  {V U : Type*} [AddCommGroup V] [Module ℤ_[q] V] [AddCommGroup U] [Module ℤ_[q] U]
  (b : Module.Basis (Fin d) ℤ_[q] V) (h : ℕ)
  (f : V →ₗ[ℤ_[q]] U) (hf : Function.Surjective f)
  (hker : f.ker = IsogenyQuotient.Basis.Construction.basisDiagonalSubmodule q b (fun _ => h))

def exactResidueCoordinates : U ≃+ (Fin d → ZMod (q ^ h)) :=
  ((f.quotKerEquivOfSurjective hf).toAddEquiv.symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq (congrArg Submodule.toAddSubgroup hker))).trans
      (IsogenyQuotient.Basis.Construction.basisDiagonalQuotientEquiv q b (fun _ => h))

theorem exactResidueCoordinates_apply (x : V) :
    exactResidueCoordinates q b h f hf hker (f x) = IsogenyQuotient.Basis.Construction.basisCoordinateResidues q b (fun _ => h) x := by
  have hx : f.quotKerEquivOfSurjective hf (Submodule.Quotient.mk x) = f x := rfl
  rw [← hx]
  change IsogenyQuotient.Basis.Construction.basisDiagonalQuotientEquiv q b (fun _ => h)
    ((QuotientAddGroup.quotientAddEquivOfEq (congrArg Submodule.toAddSubgroup hker))
      ((f.quotKerEquivOfSurjective hf).symm
        (f.quotKerEquivOfSurjective hf (Submodule.Quotient.mk x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ExactResidueCoordinates.Construction
