import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SchemeGenericFlatness
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePresentation

/-! # Field Multiplication Flat -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction

noncomputable section

/-! Flatness of finite multiplication maps on geometric fibers in Openness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type*} [Field K] [IsAlgClosed K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- A finite multiplication map on a smooth proper connected commutative
group over an algebraically closed field is surjective and flat. -/
theorem surjective_flat_multiplication_of_isFinite (n : ℕ)
    [IsFinite (Multiplication.Construction.multiplicationMap A n).left] :
    Surjective (Multiplication.Construction.multiplicationMap A n).left ∧ Flat (Multiplication.Construction.multiplicationMap A n).left := by
  have : IsIntegral A.left := ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := ⟨⟩
  have hs : Surjective (Multiplication.Construction.multiplicationMap A n).left :=
    FiniteEndomorphism.Construction.surjective_finite_endomorphism_of_isIntegral (Multiplication.Construction.multiplicationMap A n).left
  have : LocallyOfFinitePresentation (Multiplication.Construction.multiplicationMap A n).left :=
    FinitePresentation.Construction.locallyOfFinitePresentation_multiplication A n
  obtain ⟨U, hU, hfU⟩ :=
    SchemeGenericFlatness.Construction.exists_nonempty_flat_source_open_of_reduced (Multiplication.Construction.multiplicationMap A n).left
  have : Flat (U.ι ≫ (Multiplication.Construction.multiplicationMap A n).left) := hfU
  exact ⟨hs, FlatTranslations.Construction.flat_multiplication_of_nonempty_flat_open A n U hU⟩

/-- Finiteness of the torsion kernel suffices for flatness of multiplication
on a smooth proper connected geometric fiber. -/
theorem flat_multiplication_of_isFinite_torsion_over_algClosed (n : ℕ)
    [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] : Flat (Multiplication.Construction.multiplicationMap A n).left := by
  have : IsFinite (Multiplication.Construction.multiplicationMap A n).left :=
    Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A n
  exact (surjective_flat_multiplication_of_isFinite A n).2

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction
