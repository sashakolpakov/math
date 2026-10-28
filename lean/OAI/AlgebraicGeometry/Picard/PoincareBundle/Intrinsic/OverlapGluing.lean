import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

/-! # Overlap Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.OverlapGluing

noncomputable section

/-!
# The overlap gluing isomorphism has the native scheme descent formula
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing

variable {X Z W : Scheme.{u}} (p q : Z ⟶ X) (r : W ⟶ Z) (M : X.Modules)

theorem nativePullback_refl (a : (Scheme.Modules.pullback p).obj M ⟶
    (Scheme.Modules.pullback q).obj M) :
    Geometric.DescentEquations.nativePullback a r (r ≫ p) (r ≫ q) rfl rfl =
      (Scheme.Modules.pullbackComp r p).inv.app M ≫ (Scheme.Modules.pullback r).map a ≫
        (Scheme.Modules.pullbackComp r q).hom.app M := by
  simp only [Geometric.DescentEquations.nativePullback, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]

variable (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)

/-- The extended gluing isomorphism uses exactly the native descent pullback morphism. -/
def HasNativeFormula : Prop :=
  (Geometric.OverlapGluing.extendedGluing p q r M σ).hom = Geometric.DescentEquations.nativePullback σ.hom r (r ≫ p) (r ≫ q) rfl rfl

theorem hasNativeFormula : HasNativeFormula p q r M σ :=
  (Geometric.OverlapGluing.extendedGluing_hasChangedHom p q r M σ).trans
    ((Category.assoc ((Scheme.Modules.pullbackComp r p).inv.app M)
      ((Scheme.Modules.pullback r).map σ.hom) ((Scheme.Modules.pullbackComp r q).hom.app M)).trans
        (nativePullback_refl p q r M σ.hom).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.OverlapGluing
