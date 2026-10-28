import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Second Kernel Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SecondKernelDimension

noncomputable section

/-! In a two-step projective presentation, the second kernel has
projective dimension two less than the presented module. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

theorem bound (R : Type u) [CommRing R] (B C M : ModuleCat.{u} R)
    [Projective B] [Projective C] (g : B →ₗ[R] C) (π : C →ₗ[R] M)
    (he : Function.Exact g π) (hπ : Function.Surjective π)
    (d : ℕ) [HasProjectiveDimensionLE M (d + 2)] :
    HasProjectiveDimensionLE (ModuleCat.of R g.ker) d := by
  let S := π.shortComplexKer
  have hS := LinearMap.shortExact_shortComplexKer hπ
  let : HasProjectiveDimensionLE (ModuleCat.of R π.ker) (d + 1) :=
    (hS.hasProjectiveDimensionLT_X₃_iff (d + 1) inferInstance).mp inferInstance
  let g' : B →ₗ[R] π.ker := g.codRestrict π.ker (fun b => (he (g b)).mpr ⟨b, rfl⟩)
  have hg' : Function.Surjective g' := by
    intro c
    obtain ⟨b, hb⟩ := (he c.val).mp c.property
    exact ⟨b, Subtype.ext hb⟩
  have hT := LinearMap.shortExact_shortComplexKer hg'
  let : HasProjectiveDimensionLE (ModuleCat.of R g'.ker) d :=
    (hT.hasProjectiveDimensionLT_X₃_iff d inferInstance).mp inferInstance
  have hk : g'.ker = g.ker := by
    ext b
    change (g' b = 0) ↔ g b = 0
    exact Subtype.ext_iff
  exact hasProjectiveDimensionLT_of_iso
    (LinearEquiv.ofEq g'.ker g.ker hk).toModuleIso (d + 1)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SecondKernelDimension
