import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryEtaleTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels

/-! # Active Etale Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction

noncomputable section

/-!
Actual native isomorphisms of ordinary active blocks transport their
intrinsic etale plane and every line. The line permutation and subgroup
isomorphisms are constructed, with the original embedding squares.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
variable {B B' B'' : Grp (Over (Spec (.of k)))}
variable (e : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B) (e' : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B')

def activeEtaleProjection : B ⟶ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q :=
  e.hom ≫ Grp.homMk (snd (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X
    (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X)

omit [Fact q.Prime] [CharP k q] in
theorem chosenActiveEtalePlane_projection :
    ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫ activeEtaleProjection k q e = 𝟙 _ := by
  apply Grp.hom_ext
  change ((AnnihilatorSheaf.Construction.splitSecondInclusion _ _).hom.hom ≫ e.inv.hom.hom) ≫
    (e.hom.hom.hom ≫ snd _ _) = 𝟙 _
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := ((Grp.forget _).mapIso e).inv_hom_id
  rw [Category.assoc, ← Category.assoc e.inv.hom.hom, he, Category.id_comp]
  exact lift_snd _ _

instance chosenActiveEtalePlane_mono : Mono (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e) :=
  mono_of_mono_fac (chosenActiveEtalePlane_projection k q e)

def activeEtaleMap (a : B ⟶ B') :
    EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ⟶ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q :=
  ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫ a ≫ activeEtaleProjection k q e'

theorem activeEtaleMap_inclusion (a : B ⟶ B') :
    activeEtaleMap k q e e' a ≫ ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e' =
      ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫ a := by
  let M := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1
  let E := EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q
  let t : E.X ⟶ M.X ⊗ E.X :=
    (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom ≫ a.hom.hom ≫ e'.hom.hom.hom
  have : Etale E.X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  have : IsReduced E.X.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field E.X.hom
  have ht : t ≫ fst M.X E.X = 1 :=
    ReducedHeightOneMaps.Construction.map_from_reduced_of_trivial_frobenius q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) _
      (Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q k 1)
  have hfac : (t ≫ snd M.X E.X) ≫ (AnnihilatorSheaf.Construction.splitSecondInclusion M E).hom.hom = t := by
    apply CartesianMonoidalCategory.hom_ext
    · change ((t ≫ snd M.X E.X) ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X)) ≫ fst M.X E.X = _
      rw [Category.assoc, lift_fst, MonObj.comp_one]
      exact ht.symm
    · change ((t ≫ snd M.X E.X) ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X)) ≫ snd M.X E.X = _
      rw [Category.assoc, lift_snd, Category.comp_id]
  apply Grp.hom_ext
  have htmap : (activeEtaleMap k q e e' a).hom.hom = t ≫ snd M.X E.X := by
    change (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom ≫ a.hom.hom ≫
      (e'.hom.hom.hom ≫ snd M.X E.X) = _
    simp only [t, Category.assoc]
  have he' : e'.hom.hom.hom ≫ e'.inv.hom.hom = 𝟙 B'.X :=
    ((Grp.forget _).mapIso e').hom_inv_id
  change (activeEtaleMap k q e e' a).hom.hom ≫
    ((AnnihilatorSheaf.Construction.splitSecondInclusion M E).hom.hom ≫ e'.inv.hom.hom) = _
  rw [htmap, ← Category.assoc, hfac]
  change ((ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom ≫ a.hom.hom ≫ e'.hom.hom.hom) ≫
    e'.inv.hom.hom = (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom ≫ a.hom.hom
  rw [Category.assoc, Category.assoc, he', Category.comp_id]

omit [Fact q.Prime] [CharP k q] in
theorem activeEtaleMap_id : activeEtaleMap k q e e (𝟙 B) = 𝟙 _ := by
  change ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫ 𝟙 B ≫ activeEtaleProjection k q e = _
  rw [Category.id_comp, chosenActiveEtalePlane_projection]

theorem activeEtaleMap_comp (e'' : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B'')
    (a : B ⟶ B') (b : B' ⟶ B'') :
    activeEtaleMap k q e e' a ≫ activeEtaleMap k q e' e'' b =
      activeEtaleMap k q e e'' (a ≫ b) := by
  apply (cancel_mono (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e'')).mp
  rw [Category.assoc, activeEtaleMap_inclusion, ← Category.assoc,
    activeEtaleMap_inclusion, Category.assoc, activeEtaleMap_inclusion]

/-- The plane isomorphism is derived from the actual source map. -/
def activeEtaleIso (a : B ≅ B') :
    EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ≅ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q where
  hom := activeEtaleMap k q e e' a.hom
  inv := activeEtaleMap k q e' e a.inv
  hom_inv_id := by rw [activeEtaleMap_comp, a.hom_inv_id, activeEtaleMap_id]
  inv_hom_id := by rw [activeEtaleMap_comp, a.inv_hom_id, activeEtaleMap_id]

def chosenActiveLineEquiv (a : B ≅ B') : EtaleSubgroups.Construction.ActiveEtaleLine q ≃ EtaleSubgroups.Construction.ActiveEtaleLine q :=
  EtaleLabelTransport.Construction.nativeActiveEtaleLineEquiv q k (activeEtaleIso k q e e' a)

def chosenActiveLineIso (a : B ≅ B') (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L ≅
      EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q (chosenActiveLineEquiv k q e e' a L) :=
  EtaleLineTransport.Construction.activeEtaleLineSchemeIso q (Spec (.of k))
    (EtaleLabelTransport.Construction.activeEtaleLinearEquiv q k (activeEtaleIso k q e e' a)) L

/-- The induced bijection on all active lines retains each original
subgroup inclusion into the source ordinary block. -/
theorem chosenActiveLineIso_inclusion (a : B ≅ B') (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (chosenActiveLineIso k q e e' a L).hom ≫
      ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e' (chosenActiveLineEquiv k q e e' a L) =
    ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L ≫ a.hom := by
  change (chosenActiveLineIso k q e e' a L).hom ≫
      (EtaleSubgroups.Construction.activeEtaleLineEmbedding _ q (chosenActiveLineEquiv k q e e' a L) ≫
        ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e') =
    (EtaleSubgroups.Construction.activeEtaleLineEmbedding _ q L ≫ ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e) ≫ a.hom
  rw [← Category.assoc]
  have h := EtaleLineTransport.Construction.nativeActiveEtaleLineIso_embedding q k (activeEtaleIso k q e e' a) L
  change (chosenActiveLineIso k q e e' a L).hom ≫
      EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q (chosenActiveLineEquiv k q e e' a L) =
    EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L ≫ (activeEtaleIso k q e e' a).hom at h
  rw [h, Category.assoc]
  exact (congrArg (fun z => EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L ≫ z)
    (activeEtaleMap_inclusion k q e e' a.hom)).trans (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction
