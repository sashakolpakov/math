import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafKernels
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AnnihilatorBaseChange

/-! # Torsion Sheaves -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionSheaves

noncomputable section

/-!
# CartierDuality: the actual torsion kernel in commutative fppf sheaves
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- Multiplication by n on a commutative fppf sheaf, in multiplicative notation. -/
def sheafPower {S : Scheme.{u}} (F : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (n : ℕ) : F ⟶ F where
  hom.app _ := CommGrpCat.ofHom (powMonoidHom n)
  hom.naturality _ _ a := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact ((F.obj.map a).hom.map_pow x n).symm

/-- Torsion is the actual categorical kernel of multiplication by n. -/
def torsionFppfAb {S : Scheme.{u}} (F : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (n : ℕ) : CommutativeSheavesAb.Construction.Schemes.FppfAb S := kernel (sheafPower F n)

/-- Multiplication on sheaves commutes with arbitrary scheme base change. -/
theorem sheafPower_baseChange {S T : Scheme.{u}} (f : T ⟶ S) (F : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (n : ℕ) :
    (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map (sheafPower F n) = sheafPower ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj F) n := rfl

/-- The actual torsion sheaf has its canonical base-change isomorphism,
without a restriction on n or on the base morphism. -/
def torsionFppfAbBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S) (F : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (n : ℕ) :
    (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj (torsionFppfAb F n) ≅ torsionFppfAb ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj F) n :=
  PreservesKernel.iso (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f) (sheafPower F n) ≪≫ kernelIsoOfEq (sheafPower_baseChange f F n)

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)

/-- The native torsion equalizer, with its represented group law. -/
def nativeTorsionGroup : Grp (Over S) := Grp.mk (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n)

instance nativeTorsionGroup_commutative : IsCommMonObj (nativeTorsionGroup G n).X :=
  TorsionQuotient.Group.TorsionGroup.commutative G.X n

/-- The actual native subgroup inclusion. -/
def nativeTorsionInclusion : nativeTorsionGroup G n ⟶ G := by
  let hm : IsMonHom (TorsionQuotient.SubgroupFunctor.torsionι G.X n) := TorsionQuotient.Group.TorsionGroup.inclusion_isMonHom G.X n
  exact @Grp.homMk (Over S) _ _ (nativeTorsionGroup G n) G (TorsionQuotient.SubgroupFunctor.torsionι G.X n) hm

instance nativeTorsionInclusion_mono : Mono (nativeTorsionInclusion G n).hom.hom :=
  inferInstanceAs (Mono (equalizer.ι ((𝟙 G.X) ^ n) (1 : G.X ⟶ G.X)))

instance nativeTorsionSheafInclusion_mono : Mono (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativeTorsionInclusion G n)) :=
  RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (nativeTorsionInclusion G n)

/-- Every native torsion section is killed by the actual sheaf power map. -/
theorem nativeTorsionSheafInclusion_zero :
    RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativeTorsionInclusion G n) ≫ sheafPower (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n = 0 := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  exact congrArg ULift.up ((TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (x ≫ TorsionQuotient.SubgroupFunctor.torsionι G.X n)).mp ⟨x, rfl⟩)

/-- The actual represented torsion scheme is the kernel of the sheaf
power map, tested on every scheme, including nonreduced ones. -/
def nativeTorsionSheafIsKernel :
    IsLimit (KernelFork.ofι (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativeTorsionInclusion G n))
      (nativeTorsionSheafInclusion_zero G n)) := by
  apply SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints
  intro T x hx
  obtain ⟨x⟩ := x
  have hx' : x ^ n = 1 := congrArg ULift.down hx
  exact ⟨ULift.up (TorsionQuotient.SubgroupFunctor.torsionLift n x hx'), congrArg ULift.up (TorsionQuotient.SubgroupFunctor.torsionLift_ι n x hx')⟩

/-- The native torsion scheme represents exactly the actual torsion
kernel in the common commutative fppf-sheaf category. -/
def nativeTorsionSheafIso :
    CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (nativeTorsionGroup G n) ≅ torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n :=
  (nativeTorsionSheafIsKernel G n).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (sheafPower (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) 0))

/-- Geometric finite local freeness of the actual native torsion kernel
gives finite locally free representability of the actual sheaf kernel. -/
theorem torsionFppfAb_finiteLocallyFree_of_native
    [IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom] [Flat (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom]
    [LocallyOfFinitePresentation (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom] :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) :=
  ⟨nativeTorsionGroup G n, nativeTorsionGroup_commutative G n,
    inferInstanceAs (IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom),
    inferInstanceAs (Flat (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom),
    inferInstanceAs (LocallyOfFinitePresentation (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom),
    ⟨nativeTorsionSheafIso G n⟩⟩

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionSheaves
