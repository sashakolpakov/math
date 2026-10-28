import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-! # Dimension Functor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.DimensionFunctor

noncomputable section

/-! Exact additive functors preserving projective modules do not increase
projective dimension. The proof uses projective presentations and their
actual kernel short exact sequences. -/

open _root_.CategoryTheory

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

theorem preserves_bound (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    [F.PreservesHomology] [F.PreservesProjectiveObjects]
    (M : ModuleCat R) (d : ℕ) [HasProjectiveDimensionLE M d] :
    HasProjectiveDimensionLE (F.obj M) d := by
  let : Limits.PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  induction d generalizing M with
  | zero =>
    let : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
    exact (projective_iff_hasProjectiveDimensionLE_zero (F.obj M)).mp inferInstance
  | succ d ih =>
    let T := M.projectiveShortComplex
    have hT := M.shortExact_projectiveShortComplex
    let : Mono T.f := hT.mono_f
    let : Epi T.g := hT.epi_g
    let : HasProjectiveDimensionLE T.X₁ d :=
      (hT.hasProjectiveDimensionLT_X₃_iff d inferInstance).mp inferInstance
    have hleft := ih T.X₁
    let : Projective (F.obj T.X₂) := F.projective_obj_of_projective inferInstance
    let : HasProjectiveDimensionLT (F.obj T.X₂) 1 :=
      (projective_iff_hasProjectiveDimensionLT_one (X := F.obj T.X₂)).mp inferInstance
    exact (hT.map F).hasProjectiveDimensionLT_X₃ (d + 1) hleft
      (hasProjectiveDimensionLT_of_ge (F.obj T.X₂) 1 (d + 1 + 1) (by omega))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.DimensionFunctor
