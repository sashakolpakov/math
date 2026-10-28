import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedIntrinsicSubgroup
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionBaseChange

/-! # Torsion Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction

noncomputable section

/-!
The original IsogenyQuotient torsion kernels commute with arbitrary base change.
The comparison retains the native inclusion and every original restricted
group map, so a single source pairing can be used on its actual fibers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative

variable {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)

local instance nativeTorsionPullback_commutative : IsCommMonObj ((Over.pullback f).obj G.X) :=
  Functor.isCommMonObj_obj (F := Over.pullback f) (M := G.X)

def nativeTorsionBaseChangeIso :
    (Over.pullback f).obj (Torsion.Groups.Construction.nativeTorsionScheme G.X n) ≅
      Torsion.Groups.Construction.nativeTorsionScheme ((Over.pullback f).obj G.X) n :=
  (Over.pullback f).mapIso (Torsion.Groups.Construction.torsionEqualizerKernelIso G.X n).symm ≪≫
    CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.torsionBaseChangeIso f G.X n ≪≫
      Torsion.Groups.Construction.torsionEqualizerKernelIso ((Over.pullback f).obj G.X) n

theorem nativeTorsionBaseChangeIso_inclusion :
    (nativeTorsionBaseChangeIso f G n).hom ≫
      Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback f).obj G.X) n =
        (Over.pullback f).map (Torsion.Groups.Construction.nativeTorsionInclusion G.X n) := by
  change ((Over.pullback f).map (Torsion.Groups.Construction.torsionEqualizerKernelIso G.X n).inv ≫
    (CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.torsionBaseChangeIso f G.X n).hom ≫
      (Torsion.Groups.Construction.torsionEqualizerKernelIso ((Over.pullback f).obj G.X) n).hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, TorsionComparison.Construction.torsionEqualizerKernelIso_hom_inclusion,
    CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.torsionBaseChangeIso_inclusion, ← Functor.map_comp,
    TorsionComparison.Construction.torsionEqualizerKernelIso_inv_inclusion]

instance nativeTorsionBaseChangeIso_isMonHom : IsMonHom (nativeTorsionBaseChangeIso f G n).hom :=
  SupportedIntrinsicSubgroup.Construction.isMonHom_of_mono_factorization (nativeTorsionBaseChangeIso f G n).hom
    (Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback f).obj G.X) n)
    ((Over.pullback f).map (Torsion.Groups.Construction.nativeTorsionInclusion G.X n))
    (nativeTorsionBaseChangeIso_inclusion f G n)

def nativeTorsionBaseChangeGroupIso :
    (Over.pullback f).mapGrp.obj (Torsion.SheafComparison.Construction.kernelTorsionGroup G n) ≅
      Torsion.SheafComparison.Construction.kernelTorsionGroup ((Over.pullback f).mapGrp.obj G) n :=
  Grp.mkIso' (nativeTorsionBaseChangeIso f G n)

theorem nativeTorsionBaseChangeIso_inv_inclusion :
    (nativeTorsionBaseChangeIso f G n).inv ≫ (Over.pullback f).map (Torsion.Groups.Construction.nativeTorsionInclusion G.X n) =
      Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback f).obj G.X) n := by
  rw [← nativeTorsionBaseChangeIso_inclusion, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable (H : Grp (Over S)) [IsCommMonObj H.X] (a : G ⟶ H)

theorem nativeTorsionBaseChangeIso_natural :
    (Over.pullback f).map (Torsion.Groups.Construction.nativeTorsionMap n a.hom.hom) ≫ (nativeTorsionBaseChangeIso f H n).hom =
      (nativeTorsionBaseChangeIso f G n).hom ≫
        Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback f).map a.hom.hom) := by
  apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback f).obj H.X) n)).mp
  rw [Category.assoc, nativeTorsionBaseChangeIso_inclusion, ← Functor.map_comp,
    Torsion.Groups.Construction.nativeTorsionMap_inclusion, Functor.map_comp, Category.assoc, Torsion.Groups.Construction.nativeTorsionMap_inclusion,
    ← Category.assoc, nativeTorsionBaseChangeIso_inclusion]

theorem nativeTorsionBaseChangeIso_inv_natural :
    Torsion.Groups.Construction.nativeTorsionMap n ((Over.pullback f).map a.hom.hom) ≫ (nativeTorsionBaseChangeIso f H n).inv =
      (nativeTorsionBaseChangeIso f G n).inv ≫ (Over.pullback f).map (Torsion.Groups.Construction.nativeTorsionMap n a.hom.hom) := by
  apply (cancel_epi (nativeTorsionBaseChangeIso f G n).hom).mp
  rw [← Category.assoc, ← nativeTorsionBaseChangeIso_natural, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction
