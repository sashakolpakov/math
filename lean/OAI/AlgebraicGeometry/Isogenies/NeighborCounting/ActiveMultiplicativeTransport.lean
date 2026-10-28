import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtaleTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFactorization

/-! # Active Multiplicative Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeTransport

noncomputable section

/-! The multiplicative factor of an ordinary active q-block is
intrinsic. Its isomorphism is constructed from the actual block map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable (k : Type) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
  {B B' B'' : Grp (Over (Spec (.of k)))}
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B) (e' : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B')

def activeMultiplicativeProjection : B ⟶ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 :=
  e.hom ≫ Grp.homMk (fst (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X)

omit [Fact q.Prime] [CharP k q] in
theorem chosenActiveMultiplicative_projection :
    AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e ≫ activeMultiplicativeProjection k q e = 𝟙 _ := by
  apply Grp.hom_ext
  change ((AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion _ _).hom.hom ≫ e.inv.hom.hom) ≫
    (e.hom.hom.hom ≫ fst _ _) = 𝟙 _
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := ((Grp.forget _).mapIso e).inv_hom_id
  rw [Category.assoc, ← Category.assoc e.inv.hom.hom, he, Category.id_comp]
  exact lift_fst _ _

instance chosenActiveMultiplicative_mono : Mono (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e) :=
  mono_of_mono_fac (chosenActiveMultiplicative_projection k q e)

def activeMultiplicativeMap (a : B ⟶ B') :
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⟶ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 :=
  AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e ≫ a ≫ activeMultiplicativeProjection k q e'

theorem activeMultiplicativeMap_inclusion (a : B ⟶ B') :
    activeMultiplicativeMap k q e e' a ≫ AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e' =
      AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e ≫ a := by
  let M := AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1
  let E := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q
  have : Etale E.X.hom := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  obtain ⟨h, hh⟩ := AbelianScheme.FrobeniusKernel.OrdinaryFactorization.Construction.splitFactor_of_trivialFrobenius q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) e'
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e ≫ a) (AbelianScheme.FrobeniusKernel.Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q k 1)
  let i := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e').hom.hom
  let p := (activeMultiplicativeProjection k q e').hom.hom
  let t := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e ≫ a).hom.hom
  have hp : i ≫ p = 𝟙 M.X :=
    congrArg (fun f => f.hom.hom) (chosenActiveMultiplicative_projection k q e')
  have ht : h ≫ i = t := hh
  apply Grp.hom_ext
  change (t ≫ p) ≫ i = t
  calc
    (t ≫ p) ≫ i = ((h ≫ i) ≫ p) ≫ i :=
      congrArg (fun f => (f ≫ p) ≫ i) ht.symm
    _ = h ≫ i := by rw [Category.assoc h i p, hp, Category.comp_id]
    _ = t := ht

omit [Fact q.Prime] [CharP k q] in
theorem activeMultiplicativeMap_id : activeMultiplicativeMap k q e e (𝟙 B) = 𝟙 _ := by
  change AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e ≫ 𝟙 B ≫ activeMultiplicativeProjection k q e = _
  rw [Category.id_comp, chosenActiveMultiplicative_projection]

theorem activeMultiplicativeMap_comp (e'' : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B'')
    (a : B ⟶ B') (b : B' ⟶ B'') :
    activeMultiplicativeMap k q e e' a ≫ activeMultiplicativeMap k q e' e'' b =
      activeMultiplicativeMap k q e e'' (a ≫ b) := by
  apply (cancel_mono (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e'')).mp
  rw [Category.assoc, activeMultiplicativeMap_inclusion, ← Category.assoc,
    activeMultiplicativeMap_inclusion, Category.assoc, activeMultiplicativeMap_inclusion]

def activeMultiplicativeIso (a : B ≅ B') :
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ≅ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 where
  hom := activeMultiplicativeMap k q e e' a.hom
  inv := activeMultiplicativeMap k q e' e a.inv
  hom_inv_id := by rw [activeMultiplicativeMap_comp, a.hom_inv_id, activeMultiplicativeMap_id]
  inv_hom_id := by rw [activeMultiplicativeMap_comp, a.inv_hom_id, activeMultiplicativeMap_id]

theorem activeMultiplicativeIso_inclusion (a : B ≅ B') :
    (activeMultiplicativeIso k q e e' a).hom ≫ AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e' =
      AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e ≫ a.hom :=
  activeMultiplicativeMap_inclusion k q e e' a.hom

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeTransport
