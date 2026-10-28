import OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantMorphismExt
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

/-! # Invariant Morphism Ext -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.InvariantMorphismExt

noncomputable section

/-!
# Morphisms into a genuine geometric invariant are detected by their pullbacks
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  (M : X.Modules) (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)

/-- The actual geometric invariant comparison detects equality of maps into the invariant. -/
theorem hom_ext {N : Y.Modules} (k l : N ⟶ CechInvariant.invariantSheaf f p q h M σ)
    (he : (Scheme.Modules.pullback f).map k ≫ CechInvariant.comparison f p q h M σ =
      (Scheme.Modules.pullback f).map l ≫ CechInvariant.comparison f p q h M σ) : k = l :=
  PoincareBundle.InvariantMorphismExt.hom_ext (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
    (CechInvariant.directImageIso f p q h) σ.hom k l he

/-- A genuine invariant recovery makes geometric pullback injective on morphisms into the recovered sheaf. -/
theorem hom_ext_of_recovery {N K : Y.Modules} (r : K ≅ CechInvariant.invariantSheaf f p q h M σ) (k l : N ⟶ K)
    (he : (Scheme.Modules.pullback f).map k = (Scheme.Modules.pullback f).map l) : k = l :=
  PoincareBundle.InvariantMorphismExt.hom_ext_of_recovery (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
    (CechInvariant.directImageIso f p q h) σ.hom r k l he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.InvariantMorphismExt
