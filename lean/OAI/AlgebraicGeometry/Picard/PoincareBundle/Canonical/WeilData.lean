import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.StandardWeilValue

/-! # Weil Data -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilData

noncomputable section

/-! The canonical actual Cartier representative and standard Weil pairing are constructed from the original isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {k : Type} [Field k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n)

/-- The actual finite locally free Cartier representative is supplied by proved character representability. -/
def representative : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
    (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))) := by
  have h := Reference.Torsion.native_kernel D ell n hn
  have : IsFinite (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)).hom := h.1
  have : Flat (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)).hom := h.2.1
  have : LocallyOfFinitePresentation (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)).hom := h.2.2
  have : IsCommMonObj (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) :=
    Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative ((𝟙 A.scheme) ^ n)
  exact CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))

variable [IsAlgClosed k]

/-- The actual standard Weil value uses the constructed Cartier representative and constructed torsion geometry. -/
def value {T : Over (Spec (.of k))} (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb (Spec (.of k))).obj.obj (.op T) :=
  Reference.StandardWeilValue.value D ell n hn (representative D ell n hn) x y

/-- Maximal isotropy for the canonical actual standard Weil pairing is tested after every change of test scheme. -/
def SelfAnnihilating {H : Over (Spec (.of k))} (i : H ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) : Prop :=
  Reference.StandardWeilValue.SelfAnnihilating D ell n hn (representative D ell n hn) i

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilData
