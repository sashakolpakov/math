import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafComparison

/-! # Action Block Torsion Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion

noncomputable section

/-! Retain the literal fixed-point inclusion of an original coefficient
block into native torsion, as a morphism of the actual group schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso

variable {O : Type} [CommRing O] {S : Scheme} {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (n : ℕ) (a : O)

instance nativeActionBlockGroup_commutative : IsCommMonObj (Lifted.GeometricBlockIso.nativeActionBlockGroup A ρ n a).X :=
  inferInstanceAs (IsCommMonObj (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map a)))

def nativeActionBlockTorsionInclusion :
    Lifted.GeometricBlockIso.nativeActionBlockGroup A ρ n a ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.scheme) n := by
  let i := Grp.ofHom (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (ρ.map a)))
  exact i

theorem nativeActionBlockTorsionInclusion_hom :
    (nativeActionBlockTorsionInclusion A ρ n a).hom.hom =
      AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (ρ.map a)) := rfl

theorem nativeActionBlockTorsionInclusion_inclusion :
    (nativeActionBlockTorsionInclusion A ρ n a).hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n =
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map a) := rfl

def nativeActionBlockAmbientInclusion :
    Lifted.GeometricBlockIso.nativeActionBlockGroup A ρ n a ⟶ Grp.mk A.scheme := by
  let i := Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map a))
  exact i

theorem nativeActionBlockAmbientInclusion_hom :
    (nativeActionBlockAmbientInclusion A ρ n a).hom.hom = AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map a) := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion
