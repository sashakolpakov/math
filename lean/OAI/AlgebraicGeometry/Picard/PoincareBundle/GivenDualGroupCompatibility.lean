import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DualDataEquality

/-! # Given Dual Group Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GivenDualGroupCompatibility

noncomputable section

/-! Original homomorphisms and powers retain their actual maps in the Picard-derived dual group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A : Over (Spec (.of k))} [GrpObj A] (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)

/-- The given group homomorphism remains a homomorphism for the actual Picard-derived dual group law. -/
theorem isMonHom (φ : A ⟶ D.abelian) [IsMonHom φ] :
    @IsMonHom (Over (Spec (.of k))) _ _ A D.abelian _ (Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D).toMonObj φ := by
  rw [Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D]
  infer_instance

/-- Natural-number powers calculated with the Picard-derived dual group equal the given powers. -/
theorem pow_eq {T : Over (Spec (.of k))} (x : T ⟶ D.abelian) (n : ℕ) :
    let y := x ^ n
    letI := Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    x ^ n = y := by
  dsimp only
  rw [Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GivenDualGroupCompatibility
