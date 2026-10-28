import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic

/-! # Coefficient Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoefficientExtension

noncomputable section

/-! Enlarge a finite coefficient algebra to contain a specified finite list. -/

universe u v w
variable {B : Type u} [CommRing B] {R : Type v} [CommRing R] [Algebra B R]
variable (C : Subalgebra B R) {ι : Type w} [Finite ι] (x : ι → R)

def finiteCoefficientExtension : Subalgebra B R := C ⊔ Algebra.adjoin B (Set.range x)

omit [Finite ι] in
theorem le_finiteCoefficientExtension : C ≤ finiteCoefficientExtension C x := le_sup_left

omit [Finite ι] in
theorem mem_finiteCoefficientExtension (i : ι) : x i ∈ finiteCoefficientExtension C x :=
  (show Algebra.adjoin B (Set.range x) ≤ finiteCoefficientExtension C x from le_sup_right)
    (Algebra.subset_adjoin (Set.mem_range_self i))

instance finiteCoefficientExtension_finiteType [Algebra.FiniteType B C] :
    Algebra.FiniteType B (finiteCoefficientExtension C x) := by
  apply (Subalgebra.fg_iff_finiteType _).mp
  apply ((Subalgebra.fg_iff_finiteType C).mpr inferInstance).sup
  exact Subalgebra.fg_def.mpr ⟨Set.range x, Set.finite_range x, rfl⟩

instance finiteCoefficientExtension_isNoetherian [IsNoetherianRing B] [Algebra.FiniteType B C] :
    IsNoetherianRing (finiteCoefficientExtension C x) :=
  Algebra.FiniteType.isNoetherianRing B _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoefficientExtension
