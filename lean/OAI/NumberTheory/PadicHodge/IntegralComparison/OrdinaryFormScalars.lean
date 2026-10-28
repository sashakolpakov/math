import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Ordinary Form Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars.Ordinary

noncomputable section

/-!
# IntegralComparison: ordinary differential-form pullback respects ambient scalars
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R C D : Type u) [CommRing R] [CommRing C] [CommRing D]
  [Algebra R C] [Algebra R D] (f : C →ₐ[R] D)

theorem formMap_smul (n : ℕ) (a : C) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R C n) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom f) n (a • ω) =
      f a • AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom f) n ω := by
  obtain ⟨t, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R C n).mkQ_surjective ω
  change (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R D n).mkQ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.rawMap (CommAlgCat.ofHom f) n (a • t)) =
    f a • (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R D n).mkQ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.rawMap (CommAlgCat.ofHom f) n t)
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.rawMap_smul, map_smul]
  rfl

variable [Algebra C D] [IsScalarTower R C D]

def map (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R C n →ₗ[C] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R D n where
  toFun := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R C D)) n
  map_add' := fun _ _ => map_add _ _ _
  map_smul' := by
    intro a ω
    exact (formMap_smul R C D (IsScalarTower.toAlgHom R C D) n a ω).trans
      (IsScalarTower.algebraMap_smul D a _)

theorem map_symbol (n : ℕ) (a : C) (v : Fin n → C) :
    map R C D n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R C a v) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R D (algebraMap C D a) (fun i => algebraMap C D (v i)) :=
  AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol (CommAlgCat.ofHom (IsScalarTower.toAlgHom R C D)) n a v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars.Ordinary
