import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Intrinsic Torsion Functor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor.Construction

noncomputable section

/-! The native equalizer torsion groups and the multiplication kernels
represent the original HilbertConstruction torsion functor, with its unchanged point values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (n : ℕ)

def nativeTorsionGroupStructureIso (X : Over S) (a b : GrpObj X)
    (ha : @IsCommMonObj (Over S) _ _ _ X a.toMonObj)
    (hb : @IsCommMonObj (Over S) _ _ _ X b.toMonObj) (h : a = b) (m : ℕ) :
    @CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup S (@Grp.mk (Over S) _ _ X a) ha m ≅
      @CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup S (@Grp.mk (Over S) _ _ X b) hb m := by
  cases h
  exact Iso.refl _

theorem nativeTorsionGroupStructureIso_inclusion (X : Over S) (a b : GrpObj X)
    (ha : @IsCommMonObj (Over S) _ _ _ X a.toMonObj)
    (hb : @IsCommMonObj (Over S) _ _ _ X b.toMonObj) (h : a = b) (m : ℕ) :
    (nativeTorsionGroupStructureIso X a b ha hb h m).hom.hom.hom ≫ @TorsionQuotient.SubgroupFunctor.torsionι S X b m =
      @TorsionQuotient.SubgroupFunctor.torsionι S X a m := by
  cases h
  exact Category.id_comp _

def nativeTorsionPointFunctorIso :
    TorsionQuotient.Group.TorsionGroup.pointFunctor A.scheme n ≅ A.torsionFunctor n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro T U t
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    rfl)

def nativeTorsionYonedaIso :
    yonedaGrp.obj (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) n) ≅ A.torsionFunctor n :=
  TorsionQuotient.Group.TorsionGroup.pointIso A.scheme n ≪≫ nativeTorsionPointFunctorIso A n

theorem nativeTorsionYonedaIso_value (T : Over S)
    (x : T ⟶ (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) n).X) :
    ((nativeTorsionYonedaIso A n).hom.app (.op T) x).val = x ≫ TorsionQuotient.SubgroupFunctor.torsionι A.scheme n := rfl

def multiplicationKernelYonedaIso :
    yonedaGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))) ≅ A.torsionFunctor n :=
  yonedaGrp.mapIso (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk A.scheme) n) ≪≫
    nativeTorsionYonedaIso A n

theorem multiplicationKernelYonedaIso_value (T : Over S)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) :
    ((multiplicationKernelYonedaIso A n).hom.app (.op T) x).val =
      x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n) := by
  change (x ≫ 𝟙 _) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n) =
    x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n)
  rw [Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor.Construction
