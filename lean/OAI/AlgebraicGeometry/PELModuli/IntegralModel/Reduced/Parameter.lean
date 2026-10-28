import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Parameter -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Parameter

noncomputable section

/-! Reduction preserves the finite-type separated geometry of an
actual parameter over a noetherian affine coefficient base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem reduced_parameter_geometry {R : Type} [CommRing R] [IsNoetherianRing R]
    (X : Over (Spec (.of R))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    IsNoetherian (Reduction.reduction X).left ∧ LocallyOfFiniteType (Reduction.reduction X).hom ∧
      QuasiCompact (Reduction.reduction X).hom ∧ IsSeparated (Reduction.reduction X).hom := by
  have hft : LocallyOfFiniteType (Reduction.reduction X).hom :=
    inferInstanceAs (LocallyOfFiniteType ((Reduction.reductionι X).left ≫ X.hom))
  have hqc : QuasiCompact (Reduction.reduction X).hom :=
    inferInstanceAs (QuasiCompact ((Reduction.reductionι X).left ≫ X.hom))
  have hsep : IsSeparated (Reduction.reduction X).hom :=
    inferInstanceAs (IsSeparated ((Reduction.reductionι X).left ≫ X.hom))
  have : IsLocallyNoetherian (Reduction.reduction X).left := LocallyOfFiniteType.isLocallyNoetherian (Reduction.reduction X).hom
  have : CompactSpace (Reduction.reduction X).left := QuasiCompact.compactSpace_of_compactSpace (Reduction.reduction X).hom
  exact ⟨⟨⟩, hft, hqc, hsep⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.Parameter
