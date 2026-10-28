import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TrivialEtaleProduct
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PulledMultiplicativeFactorInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeTransport

/-! # Multiplicative Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The mixed special kernel with zero etale submodule is the native
multiplicative factor, including its original subgroup inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TrivialEtaleProduct
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PulledMultiplicativeFactorInclusion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeTransport

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricMultiplicativeSourceIso :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj
        (C.identity ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R))
          (Multiplicative (⊥ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))) ≅
      AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 1 :=
  (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.mapIso
    (TrivialEtaleProduct.trivialEtaleProductIso C.identity (Multiplicative (⊥ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))) ≪≫
      C.geometricIdentityIso R L q A ρ

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricMultiplicative_inclusion :
    (C.geometricMultiplicativeSourceIso R L q A ρ).hom.hom.hom ≫
      (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ)).hom.hom =
      (C.geometricSpecialKernel R L q A ρ ⊥ true).inclusion := by
  let f := Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)
  let F := (Over.pullback f).mapGrp
  let G := Multiplicative (⊥ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q))
  let k := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap (Spec (.of R))
    (⊥ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)).subtype.toAddMonoidHom.toMultiplicative
  let m := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ)
  have hp : (C.geometricIdentityIso R L q A ρ).hom ≫ m =
      F.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion C.identity
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q))) ≫ C.split.hom) :=
    PulledMultiplicativeFactorInclusion.pulledSplitFirst_inclusion f C.split (C.geometricIdentityIso R L q A ρ)
      (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtaleIso R q ρ)
  have ht := TrivialEtaleProduct.trivialEtaleProduct_inclusion C.identity G k
  have h : (C.geometricMultiplicativeSourceIso R L q A ρ).hom ≫ m =
      F.map (((𝟙 C.identity) ⊗ₘ k) ≫ C.split.hom) := by
    change (F.map (TrivialEtaleProduct.trivialEtaleProductIso C.identity G).hom ≫
      (C.geometricIdentityIso R L q A ρ).hom) ≫ m = _
    rw [Category.assoc, hp, ← F.map_comp, ← Category.assoc, ht]
  exact congrArg (fun u => u.hom.hom) h

variable {B : Grp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))}
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q B)
  (a : (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A ≅ B)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricIndependentMultiplicativeIso :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj
        (C.identity ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R))
          (Multiplicative (⊥ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))) ≅
      AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 1 :=
  C.geometricMultiplicativeSourceIso R L q A ρ ≪≫
    ActiveMultiplicativeTransport.activeMultiplicativeIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricIndependentMultiplicative_inclusion :
    (C.geometricIndependentMultiplicativeIso R L q A ρ e a).hom.hom.hom ≫
      (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e).hom.hom =
      (C.geometricSpecialKernel R L q A ρ ⊥ true).inclusion ≫ a.hom.hom.hom := by
  let u := (C.geometricMultiplicativeSourceIso R L q A ρ).hom.hom.hom
  let v := (ActiveMultiplicativeTransport.activeMultiplicativeIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q
    (C.geometricSplitting R L q A ρ) e a).hom.hom.hom
  let k := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ)).hom.hom
  let h := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e).hom.hom
  have hv : v ≫ h = k ≫ a.hom.hom.hom :=
    congrArg (fun f => f.hom.hom) (ActiveMultiplicativeTransport.activeMultiplicativeIso_inclusion
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a)
  have hu : u ≫ k = (C.geometricSpecialKernel R L q A ρ ⊥ true).inclusion :=
    C.geometricMultiplicative_inclusion R L q A ρ
  exact (Category.assoc u v h).trans ((congrArg (fun f => u ≫ f) hv).trans
    ((Category.assoc u k a.hom.hom.hom).symm.trans (congrArg (fun f => f ≫ a.hom.hom.hom) hu)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
