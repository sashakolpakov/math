import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantUniversal
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.NaturalGluingCompatibility

/-! # Invariant Universal -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.InvariantUniversal.Raw

noncomputable section

/-!
# The geometric invariant universal property in arbitrary affine coordinates
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (p q : S ⟶ T)
  (h : Spec.map p ≫ Spec.map f = Spec.map q ≫ Spec.map f)
  (M : (Spec S).Modules)
  (σ : (Scheme.Modules.pullback (Spec.map p)).obj M ≅
    (Scheme.Modules.pullback (Spec.map q)).obj M)

def invariant : (Spec R).Modules :=
  Geometric.CechInvariant.invariantSheaf (Spec.map f) (Spec.map p) (Spec.map q) h M σ

def comparison : (Scheme.Modules.pullback (Spec.map f)).obj (invariant f p q h M σ) ⟶ M :=
  Geometric.CechInvariant.comparison (Spec.map f) (Spec.map p) (Spec.map q) h M σ

def Compatible {P : (Spec R).Modules} (φ : (Scheme.Modules.pullback (Spec.map f)).obj P ⟶ M) : Prop :=
  NaturalGluingCompatibility.CompatibleWith f p q φ σ.hom
    (Cech.MateNormalization.standardGluing (Spec.map f) (Spec.map p) (Spec.map q) h)

theorem comparison_compatible : Compatible f p q h M σ (comparison f p q h M σ) :=
  Geometric.NaturalGluingCompatibility.comparison_compatible (Spec.map f) (Spec.map p) (Spec.map q) h M σ

variable {P : (Spec R).Modules} (φ : (Scheme.Modules.pullback (Spec.map f)).obj P ⟶ M)

/-- The actual invariant factor selected from its proved universal property. -/
def lift (hφ : Compatible f p q h M σ φ) : P ⟶ invariant f p q h M σ :=
  (Cech.InvariantUniversal.existsUnique_lift (Spec.map f) (Spec.map p) (Spec.map q) h M σ P
    ⟨φ, hφ⟩).choose

theorem lift_fac (hφ : Compatible f p q h M σ φ) :
    (Scheme.Modules.pullback (Spec.map f)).map (lift f p q h M σ φ hφ) ≫ comparison f p q h M σ = φ :=
  (Cech.InvariantUniversal.existsUnique_lift (Spec.map f) (Spec.map p) (Spec.map q) h M σ P
    ⟨φ, hφ⟩).choose_spec.1

theorem lift_unique (hφ : Compatible f p q h M σ φ) (a b : P ⟶ invariant f p q h M σ)
    (ha : (Scheme.Modules.pullback (Spec.map f)).map a ≫ comparison f p q h M σ = φ)
    (hb : (Scheme.Modules.pullback (Spec.map f)).map b ≫ comparison f p q h M σ = φ) : a = b :=
  (Cech.InvariantUniversal.existsUnique_lift (Spec.map f) (Spec.map p) (Spec.map q) h M σ P
    ⟨φ, hφ⟩).unique ha hb

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.InvariantUniversal.Raw
