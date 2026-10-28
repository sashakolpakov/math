import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantObjectChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

/-! # Cech Object Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechObjectChange

noncomputable section

/-!
# A geometric gluing-compatible sheaf isomorphism preserves the actual invariant
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  (M N : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)
  (τ : (Scheme.Modules.pullback p).obj N ≅ (Scheme.Modules.pullback q).obj N) (x : M ≅ N)
  (hx : (Scheme.Modules.pullback p).map x.hom ≫ τ.hom = σ.hom ≫ (Scheme.Modules.pullback q).map x.hom)

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

/-- The isomorphism of original geometric sheaves induces an actual invariant isomorphism. -/
def invariantIso : CechInvariant.invariantSheaf f p q h M σ ≅ CechInvariant.invariantSheaf f p q h N τ :=
  Cech.InvariantObjectChange.invariantIso (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction q) (CechInvariant.directImageIso f p q h) σ.hom τ.hom x hx

/-- The actual canonical comparison retains the specified original sheaf isomorphism. -/
theorem comparison_fac :
    (Scheme.Modules.pullback f).map (invariantIso f p q h M N σ τ x hx).hom ≫ CechInvariant.comparison f p q h N τ =
      CechInvariant.comparison f p q h M σ ≫ x.hom :=
  Cech.InvariantObjectChange.comparison_fac (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
    (CechInvariant.directImageIso f p q h) σ.hom τ.hom x hx

include hx in
/-- A gluing-compatible geometric sheaf isomorphism preserves effectivity. -/
theorem comparison_isIso_iff :
    IsIso (CechInvariant.comparison f p q h M σ) ↔ IsIso (CechInvariant.comparison f p q h N τ) :=
  Cech.InvariantObjectChange.comparison_isIso_iff (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
    (CechInvariant.directImageIso f p q h) σ.hom τ.hom x hx

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechObjectChange
