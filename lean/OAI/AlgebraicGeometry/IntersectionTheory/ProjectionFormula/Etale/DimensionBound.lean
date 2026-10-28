import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.DimensionBound
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Flat.Localization

/-! # Dimension Bound -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DimensionBound

noncomputable section

/-! Flat essentially finite-type unramified extensions preserve the global
projective-dimension bound: every target module is a retract of its scalar
extension from the source. This includes localizations and étale charts. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.DimensionBound

theorem extension_bound (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    (d : ℕ) (h : Polynomial.DimensionBound.GlobalBound R d) : Polynomial.DimensionBound.GlobalBound S d := by
  intro M
  let : Module R M := Module.compHom M (algebraMap R S)
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (by intros; rfl)
  let : HasProjectiveDimensionLE (ModuleCat.of R M) d := h (ModuleCat.of R M)
  let : HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] M)) d :=
    Projective.DimensionFunctor.preserves_bound (ProjectionFormula.Flat.Extension.baseChange R S)
      (ModuleCat.of R M) d
  let e : Retract M (ModuleCat.of S (S ⊗[R] M)) :=
    { i := ModuleCat.ofHom (Algebra.FormallyUnramified.sec R S M)
      r := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lift
        ((Algebra.lsmul S S M).toLinearMap.flip.restrictScalars R).flip)
      retract := ModuleCat.hom_ext (Algebra.FormallyUnramified.comp_sec R S M) }
  exact e.hasProjectiveDimensionLT (d + 1)

theorem localization_bound (R : Type u) [CommRing R] (T : Submonoid R)
    (d : ℕ) (h : Polynomial.DimensionBound.GlobalBound R d) : Polynomial.DimensionBound.GlobalBound (Localization T) d :=
  extension_bound R (Localization T) d h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DimensionBound
