import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.WeilPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Torsion

/-! # Standard Weil Value -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.StandardWeilValue

noncomputable section

/-! The given isogeny and a positive integer determine the standard Weil value with all torsion geometry constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n)
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
    (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))))

/-- The actual Weil value requires no separately assumed finiteness, flatness, or reducedness of torsion. -/
def value {T : Over (Spec (.of k))} (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb (Spec (.of k))).obj.obj (.op T) := by
  have h := Torsion.cover D ell n hn
  have : IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.1
  have : Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.1
  have : Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.2.2.1
  have : IsAffine (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).left := h.2.2.2.2
  exact WeilPairing.value D ell n hn C x y

/-- Standard Weil self-annihilation is imposed on the full represented torsion subgroup after every test-scheme restriction. -/
def SelfAnnihilating {H : Over (Spec (.of k))} (i : H ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) : Prop :=
  ∀ (T : Over (Spec (.of k))) (y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)),
    (∀ (U : Over (Spec (.of k))) (a : U ⟶ T) (x : U ⟶ H), value D ell n hn C (x ≫ i) (a ≫ y) = 1) ↔
      ∃ x : T ⟶ H, x ≫ i = y

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.StandardWeilValue
