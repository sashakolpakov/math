import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Pairing
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps

/-! # Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction

noncomputable section

/-!
The native torsion scheme used by IsogenyQuotient represents CartierDuality's actual fppf
sheaf kernel of multiplication. The canonical comparison preserves
the original subgroup inclusion and every original group homomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)

def kernelTorsionGroup : Grp (Over S) := Grp.mk (Groups.Construction.nativeTorsionScheme G.X n)

instance kernelTorsionGroup_commutative : IsCommMonObj (kernelTorsionGroup G n).X :=
  Groups.Construction.nativeTorsionScheme_commutative G.X n

def kernelTorsionInclusion : kernelTorsionGroup G n ⟶ G :=
  @Grp.homMk (Over S) _ _ (kernelTorsionGroup G n) G
    (Groups.Construction.nativeTorsionInclusion G.X n) (Groups.Construction.nativeTorsionInclusion_isMonHom G.X n)

instance kernelTorsionInclusion_mono : Mono (kernelTorsionInclusion G n).hom.hom :=
  Groups.Construction.nativeTorsionInclusion_mono G.X n

theorem kernelTorsionSheafInclusion_zero :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelTorsionInclusion G n) ≫ CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n = 0 := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  change T.unop ⟶ Groups.Construction.nativeTorsionScheme G.X n at x
  apply congrArg ULift.up
  change (x ≫ Groups.Construction.nativeTorsionInclusion G.X n) ^ n = 1
  exact (MonObj.comp_pow (Groups.Construction.nativeTorsionInclusion G.X n) n x).symm.trans
    ((congrArg (fun k => x ≫ k) (Groups.Construction.nativeTorsionInclusion_killed G.X n)).trans (MonObj.comp_one x))

def kernelTorsionSheafIsKernel :
    IsLimit (KernelFork.ofι (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelTorsionInclusion G n))
      (kernelTorsionSheafInclusion_zero G n)) := by
  let : Mono (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelTorsionInclusion G n)) :=
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (kernelTorsionInclusion G n)
  apply CartierDuality.SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints
  intro T x hx
  obtain ⟨x⟩ := x
  change T ⟶ G.X at x
  have hx' : x ^ n = 1 := congrArg ULift.down hx
  exact ⟨ULift.up (Groups.Construction.nativeTorsionLift G.X n x hx'),
    congrArg ULift.up (Groups.Construction.nativeTorsionLift_inclusion G.X n x hx')⟩

def kernelTorsionSheafIso :
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (kernelTorsionGroup G n) ≅ CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n :=
  (kernelTorsionSheafIsKernel G n).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) 0))

theorem kernelTorsionSheafIso_inclusion :
    (kernelTorsionSheafIso G n).hom ≫ kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelTorsionInclusion G n) :=
  (kernelTorsionSheafIsKernel G n).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (parallelPair (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) 0)) WalkingParallelPair.zero

variable {G} {K : Grp (Over S)} [IsCommMonObj K.X]

def kernelTorsionGroupMap (f : G ⟶ K) : kernelTorsionGroup G n ⟶ kernelTorsionGroup K n :=
  @Grp.homMk (Over S) _ _ (kernelTorsionGroup G n) (kernelTorsionGroup K n)
    (Groups.Construction.nativeTorsionMap n f.hom.hom) (Groups.Construction.nativeTorsionMap_isMonHom n f.hom.hom)

theorem kernelTorsionGroupMap_inclusion (f : G ⟶ K) :
    kernelTorsionGroupMap n f ≫ kernelTorsionInclusion K n = kernelTorsionInclusion G n ≫ f := by
  apply Grp.hom_ext
  exact Groups.Construction.nativeTorsionMap_inclusion n f.hom.hom

theorem kernelTorsionSheafIso_natural (f : G ⟶ K) :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelTorsionGroupMap n f) ≫ (kernelTorsionSheafIso K n).hom =
      (kernelTorsionSheafIso G n).hom ≫ CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) n := by
  have hm : Mono (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) n)) :=
    inferInstanceAs (Mono (equalizer.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) n) 0))
  apply @CartierDuality.SheafTorsionMaps.Construction.Schemes.inclusion_comparison_natural (CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) inferInstance _ _ _ _ _ _
    (kernelTorsionSheafIso G n).hom (kernelTorsionSheafIso K n).hom
    (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n))
    (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) n)) hm
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelTorsionInclusion G n))
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelTorsionInclusion K n)) (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f)
    _ _ (kernelTorsionSheafIso_inclusion G n) (kernelTorsionSheafIso_inclusion K n)
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap_inclusion (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) n)
  exact (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp (kernelTorsionGroupMap n f) (kernelTorsionInclusion K n)).symm.trans
    ((congrArg CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (kernelTorsionGroupMap_inclusion n f)).trans
      (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp (kernelTorsionInclusion G n) f))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction
