import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant

/-! # Invariant Morphism Ext -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantMorphismExt

noncomputable section

/-!
# Morphisms into an actual invariant are determined by their recovered pullbacks
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {L : C ⥤ D} {R : D ⥤ C} {P Q : D ⥤ E} {U V : E ⥤ D}
  (a : L ⊣ R) (b : P ⊣ U) (c : Q ⊣ V) (e : U ⋙ R ≅ V ⋙ R)
  [HasEqualizers C] {M : D} (σ : P.obj M ⟶ Q.obj M)

/-- Equality after the actual invariant comparison implies equality of the original morphisms. -/
theorem hom_ext {N : C} (k l : N ⟶ AdjointCechInvariant.invariants b c e σ)
    (h : L.map k ≫ AdjointCechInvariant.comparison a b c e σ = L.map l ≫ AdjointCechInvariant.comparison a b c e σ) : k = l := by
  apply equalizer.hom_ext
  exact (AdjointCechInvariant.homEquiv_map_comparison a b c e σ k).symm.trans
    ((congrArg (a.homEquiv N M) h).trans (AdjointCechInvariant.homEquiv_map_comparison a b c e σ l))

include a in
/-- A specified actual invariant recovery makes pullback injective on maps into the recovered object. -/
theorem hom_ext_of_recovery {N K : C} (r : K ≅ AdjointCechInvariant.invariants b c e σ) (k l : N ⟶ K)
    (h : L.map k = L.map l) : k = l := by
  apply (cancel_mono r.hom).mp
  apply InvariantMorphismExt.hom_ext a b c e σ
  rw [L.map_comp, L.map_comp, h]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantMorphismExt
