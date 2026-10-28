import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! # Integral Rational Basis -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntegralRationalBasis

noncomputable section

/-! An integral basis of a full rational lattice, of the expected rank,
is a rational basis with exactly the same integral span. -/

open _root_.Module _root_.Submodule

variable {V I : Type*} [AddCommGroup V] [Module ℚ V] [Fintype I]
    (L : Submodule ℤ V) (b : Basis I ℤ L)

omit [Module ℚ V] [Fintype I] in
theorem integralBasis_span : Submodule.span ℤ (Set.range fun i => (b i : V)) = L := by
  calc
    Submodule.span ℤ (Set.range fun i => (b i : V)) =
        Submodule.map L.subtype (Submodule.span ℤ (Set.range b)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = L := by rw [b.span_eq, Submodule.map_top, Submodule.range_subtype]

variable (hspan : Submodule.span ℚ (L : Set V) = ⊤)
    (hrank : Fintype.card I = Module.finrank ℚ V)

def integralRationalBasis : Basis I ℚ V :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => (b i : V))
    (by rw [← Submodule.span_span_of_tower ℤ ℚ, integralBasis_span, hspan]) hrank

theorem integralRationalBasis_apply (i : I) : integralRationalBasis L b hspan hrank i = (b i : V) :=
  congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i

theorem integralRationalBasis_span :
    Submodule.span ℤ (Set.range (integralRationalBasis L b hspan hrank)) = L := by
  have hb : (integralRationalBasis L b hspan hrank : I → V) = fun i => (b i : V) :=
    funext (integralRationalBasis_apply L b hspan hrank)
  rw [hb]
  exact integralBasis_span L b

theorem integralRationalBasis_mem_iff (v : V) : v ∈ L ↔
    ∀ i, (integralRationalBasis L b hspan hrank).repr v i ∈ Set.range (algebraMap ℤ ℚ) := by
  calc
    v ∈ L ↔ v ∈ Submodule.span ℤ (Set.range (integralRationalBasis L b hspan hrank)) := by
      rw [integralRationalBasis_span]
    _ ↔ _ := (integralRationalBasis L b hspan hrank).mem_span_iff_repr_mem ℤ v

end

end OAI.RepresentationTheory.Theta.Geometric.IntegralRationalBasis
