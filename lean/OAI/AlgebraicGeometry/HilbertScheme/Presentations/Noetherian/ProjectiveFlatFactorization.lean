import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalProjectiveFlatModel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.IdealTower

/-! # Projective Flat Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.ProjectiveFlatFactorization.GradedHilbert

noncomputable section

/-! Flat projective quotients over arbitrary local rings have actual
Noetherian local flat coefficient models. The original coefficient ring
need only be Noetherian; it need not itself be local. -/

open _root_.AlgebraicGeometry

universe u
variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A] {n : ℕ}

structure NoetherianLocalFlatCoefficientModel (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading B n)) where
  R : Type u
  [commRing : CommRing R]
  [baseAlgebra : Algebra B R]
  [targetAlgebra : Algebra R A]
  [tower : IsScalarTower B R A]
  [noetherian : IsNoetherianRing R]
  [localRing : IsLocalRing R]
  [targetLocalHom : IsLocalHom (algebraMap R A)]
  flat : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I)))

attribute [instance] NoetherianLocalFlatCoefficientModel.commRing
  NoetherianLocalFlatCoefficientModel.baseAlgebra NoetherianLocalFlatCoefficientModel.targetAlgebra
  NoetherianLocalFlatCoefficientModel.tower NoetherianLocalFlatCoefficientModel.noetherian
  NoetherianLocalFlatCoefficientModel.localRing NoetherianLocalFlatCoefficientModel.targetLocalHom

theorem exists_noetherian_local_flat_coefficient_model
    [IsNoetherianRing B] [IsLocalRing A]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading B n))
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)))] :
    Nonempty (NoetherianLocalFlatCoefficientModel (A := A) I) := by
  let C := LocalCoefficientRing.localCoefficientRing (⊥ : Subalgebra B A)
  let : Algebra.FiniteType B (⊥ : Subalgebra B A) :=
    (Subalgebra.fg_iff_finiteType _).mp Subalgebra.fg_bot
  let : IsNoetherianRing C := LocalCoefficientRing.localCoefficientRing_noetherian _
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := C) I
  have : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) J))) := by
    dsimp only [J]
    rw [Homogeneous.IdealTower.GradedHilbert.extendedHomogeneousIdeal_tower]
    infer_instance
  let : Algebra.FiniteType C (⊥ : Subalgebra C A) :=
    (Subalgebra.fg_iff_finiteType _).mp Subalgebra.fg_bot
  obtain ⟨E, _, hE, hflat⟩ := LocalProjectiveFlatModel.GradedHilbert.projective_flat_local_coefficient_model J (⊥ : Subalgebra C A)
  let : Algebra.FiniteType C E := hE
  let R := LocalCoefficientRing.localCoefficientRing E
  let : Algebra B R := ((algebraMap C R).comp (algebraMap B C)).toAlgebra
  let : IsScalarTower B C R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower B R A := IsScalarTower.of_algebraMap_eq (fun b => by
    rw [IsScalarTower.algebraMap_apply B C A b]
    exact IsScalarTower.algebraMap_apply C R A (algebraMap B C b))
  refine ⟨{ R := R, flat := ?_ }⟩
  have ht : Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) J = Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I :=
    Homogeneous.IdealTower.GradedHilbert.extendedHomogeneousIdeal_tower I
  rwa [← ht]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.ProjectiveFlatFactorization.GradedHilbert
