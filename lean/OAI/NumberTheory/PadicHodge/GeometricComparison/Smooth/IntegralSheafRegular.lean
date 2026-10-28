import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Integral Sheaf Regular -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralSheafRegular.SmoothIntegralSheafRegular

noncomputable section

/-! Multiplication by a base non-zero-divisor is monic on the first two native form sheaves of a smooth scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R))) [Smooth X.hom]
  (n : ℕ) (hn : n ≤ 1) (r : R) (hr : IsRegular r)

include hn hr in
theorem locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.left)
      (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)) where
  equalizerSieve_mem {V} a b hab := by
    intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open hx V.unop.isOpen
    refine ⟨W, homOfLE hWV, ?_, hxW⟩
    change (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map (homOfLE hWV).op a =
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map (homOfLE hWV).op b
    apply IntegralSections.SmoothIntegralSections.forms_regular R X W hW n hn r hr
    change r • a = r • b at hab
    have h := congrArg ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map (homOfLE hWV).op) hab
    simpa only [map_smul] using h

include hn hr in
theorem monic : Mono (r • 𝟙 ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n)) := by
  let J := Opens.grothendieckTopology X.left
  let P := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n
  let : Presheaf.IsLocallyInjective J (r • 𝟙 P) := locallyInjective R X n hn r hr
  let : Sheaf.IsLocallyInjective ((presheafToSheaf J (ModuleCat.{u} R)).map (r • 𝟙 P)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J (r • 𝟙 P)).mpr inferInstance
  have h := Sheaf.mono_of_isLocallyInjective ((presheafToSheaf J (ModuleCat.{u} R)).map (r • 𝟙 P))
  rw [Functor.map_smul, CategoryTheory.Functor.map_id] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralSheafRegular.SmoothIntegralSheafRegular
