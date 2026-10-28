import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ExtDimensionShift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic

/-! # Module Ext -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModuleExt

/-!

# `Ext`-modules between finitely generated modules over Noetherian rings are finitely generated

-/

/- HilbertConstruction-local adaptation, using default elaboration settings. -/

universe v u

variable (R : Type u) [CommRing R]

open _root_.CategoryTheory Abelian

instance ModuleCat.finite_ext [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Finite R M] (i : ℕ) : Module.Finite R (Ext N M i) := by
  induction i generalizing N with
  | zero => exact Module.Finite.equiv (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv).symm
  | succ n ih =>
    obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R N
    let exac := LinearMap.shortExact_shortComplexKer surjf
    exact Module.Finite.of_surjective (exac.extClass.precompOfLinear R M (add_comm 1 n))
      (HilbertConstruction.Module.ExtDimensionShift.precomp_extClass_surjective_of_projective_X₂ M exac n)

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModuleExt
