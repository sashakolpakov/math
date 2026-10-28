import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf

/-! # Kernel Torsion Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison

noncomputable section

/-! Canonical comparison of the two inherited group structures on the multiplication kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

universe u

namespace Construction.Schemes

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)

/-- Both inherited group structures have the same canonical kernel inclusion. -/
def multiplicationKernelGroupIso :
    Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 G.X) ^ n)) ≅ TorsionSheaves.Construction.Schemes.nativeTorsionGroup G n := by
  let K := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 G.X) ^ n))
  let H := TorsionSheaves.Construction.Schemes.nativeTorsionGroup G n
  let e : K.X ≅ H.X := Iso.refl (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n)
  let j : H.X ⟶ G.X := TorsionQuotient.SubgroupFunctor.torsionι G.X n
  have : IsMonHom j := TorsionQuotient.Group.TorsionGroup.inclusion_isMonHom G.X n
  have : Mono j := inferInstanceAs (Mono (equalizer.ι ((𝟙 G.X) ^ n) (1 : G.X ⟶ G.X)))
  have : IsMonHom (e.hom ≫ j) := by
    change IsMonHom ((𝟙 K.X) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n))
    rw [Category.id_comp]
    infer_instance
  have : IsMonHom e.hom := Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp e.hom j
  exact Grp.mkIso' e

/-- The character-descent kernel represents the actual commutative fppf torsion sheaf. -/
def multiplicationKernelSheafIso :
    CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 G.X) ^ n))) ≅
      TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n :=
  SheafBaseChange.Construction.Schemes.representedFppfAbIso (multiplicationKernelGroupIso G n) ≪≫ TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso G n

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison
