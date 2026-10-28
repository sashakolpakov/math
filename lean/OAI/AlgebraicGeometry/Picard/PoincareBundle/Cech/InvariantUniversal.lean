import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

/-! # Invariant Universal -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantUniversal

noncomputable section

/-!
# The global invariant sheaf represents ordinary geometric descent morphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  (M : X.Modules) (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)
  (N : Y.Modules)

/-- Morphisms compatible with the ordinary geometric Čech gluing diagram. -/
def CompatibleHom :=
  { φ : (Scheme.Modules.pullback f).obj N ⟶ M //
    (Scheme.Modules.pullback p).map φ ≫ σ.hom =
      (MateNormalization.standardGluing f p q h).hom.app N ≫ (Scheme.Modules.pullback q).map φ }

/-- The adjunction formulation and the ordinary geometric formulation agree on the exact morphism. -/
def compatibilityEquiv : CompatibleHom f p q h M σ N ≃
    AdjointCechInvariant.CompatibleHom (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
      (Geometric.CechInvariant.directImageIso f p q h) N σ.hom where
  toFun φ := ⟨φ.val, by
    change (Scheme.Modules.pullback p).map φ.val ≫ σ.hom =
      (Geometric.CechInvariant.pullbackIso f p q h).hom.app N ≫ (Scheme.Modules.pullback q).map φ.val
    rw [MateNormalization.pullbackIso_eq_standard]
    exact φ.property⟩
  invFun φ := ⟨φ.val, by
    rw [← MateNormalization.pullbackIso_eq_standard]
    exact φ.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The global invariant sheaf represents all compatible maps from geometric pullbacks. -/
def invariantHomEquiv : CompatibleHom f p q h M σ N ≃ (N ⟶ Geometric.CechInvariant.invariantSheaf f p q h M σ) :=
  (compatibilityEquiv f p q h M σ N).trans
    (AdjointCechInvariant.invariantHomEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
      (Geometric.CechInvariant.directImageIso f p q h) N σ.hom)

/-- A compatible geometric morphism factors uniquely through the invariant pullback comparison. -/
theorem existsUnique_lift (φ : CompatibleHom f p q h M σ N) :
    ∃! k : N ⟶ Geometric.CechInvariant.invariantSheaf f p q h M σ,
      (Scheme.Modules.pullback f).map k ≫ Geometric.CechInvariant.comparison f p q h M σ = φ.val :=
  AdjointCechInvariant.existsUnique_lift (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction q)
    (Geometric.CechInvariant.directImageIso f p q h) σ.hom ((compatibilityEquiv f p q h M σ N) φ)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantUniversal
