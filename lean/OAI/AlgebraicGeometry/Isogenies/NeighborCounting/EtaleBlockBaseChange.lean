import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleGroupFunctor
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange

/-! # Etale Block Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBlockBaseChange

noncomputable section

/-! The original finite constant group models commute with base
change; their level-one labels are the literal q-vector spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S S' : Scheme} (f : S' ⟶ S) (G : Type) [Group G]

def constantGroupFunctorBaseChangeIso :
    (Over.map f).op ⋙ AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G ≅ AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S' G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro T U a; rfl)

def etaleBlockBaseChangeIso :
    (Over.pullback f).mapGrp.obj (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G) ≅ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S' G :=
  (yonedaGrpFullyFaithful (C := Over S')).preimageIso
    ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G)).symm ≪≫
      Functor.isoWhiskerLeft (Over.map f).op (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G) ≪≫
        constantGroupFunctorBaseChangeIso f G ≪≫ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S' G).symm)

def zmodVectorLevelEquiv (n m r : ℕ) (h : n = m) :
    (Fin r → ZMod n) ≃+ (Fin r → ZMod m) := by
  subst m
  exact AddEquiv.refl _

def ordinaryEtaleLabelsPrimeEquiv (q r : ℕ) :
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 1 r ≃* Multiplicative (Fin r → ZMod q) :=
  MulEquiv.ulift.trans ((zmodVectorLevelEquiv (q ^ 1) q r (pow_one q)).toMultiplicative)

def ordinaryEtalePrimeIso (R : Type) [CommRing R] (q r : ℕ) :
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock R q 1 r ≅ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin r → ZMod q)) :=
  AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso (Spec (.of R)) (ordinaryEtaleLabelsPrimeEquiv q r)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBlockBaseChange
