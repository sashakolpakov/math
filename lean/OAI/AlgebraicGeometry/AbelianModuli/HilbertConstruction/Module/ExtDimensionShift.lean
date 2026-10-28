import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CategoryHasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Ext Dimension Shift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ExtDimensionShift

/-!

# Dimension Shifting

-/

/- HilbertConstruction-local adaptation, using default elaboration settings. -/

universe v u

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open _root_.CategoryTheory Abelian

/-- The standard short complex `0 → N → P → M → 0` with `P= R^{⊕M}` free. -/
noncomputable abbrev ModuleCat.projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    ShortComplex (ModuleCat.{v} R) :=
  let e : Module.Basis M R (M →₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr ℕ id).shortComplexKer

theorem ModuleCat.shortExact_projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    (ExtDimensionShift.ModuleCat.projectiveShortComplex M).ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

instance [Small.{v} R] (M : ModuleCat.{v} R) : Module.Free R (ExtDimensionShift.ModuleCat.projectiveShortComplex M).X₂ :=
  Module.Free.finsupp R _ _

/-- The connection maps in the contravariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is projective. -/
theorem precomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : ℕ)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) :=
  fun x ↦ Ext.contravariant_sequence_exact₃ h M x (Ext.eq_zero_of_projective _) (add_comm 1 n)

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ExtDimensionShift
