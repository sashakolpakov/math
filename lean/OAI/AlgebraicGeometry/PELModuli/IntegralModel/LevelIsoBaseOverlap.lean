import OAI.AlgebraicGeometry.PELModuli.IntegralModel.MorphismBaseOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Level Iso Base Overlap -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelIsoBaseOverlap

noncomputable section

/-! Rigidity on the actual base overlap supplies all four descent
equations. Only reduced base tests are used for a finite etale cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

variable {S Y W : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (u : Y ⟶ S)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback u) (B.pullback u))

def levelIsoAlongAt (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (B.pullback t) := by
  subst t
  exact (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A u a).symm.trans
    ((e.pullback a).trans (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp B u a))

theorem levelIsoAlongAt_abelian_hom (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t) :
    (levelIsoAlongAt A B u e a t w).abelian.hom = AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt A.abelian.scheme u a t w e.abelian.hom := by
  subst t
  change (A.abelian.pullbackCompIso u a).hom ≫ (Over.pullback a).map e.abelian.hom ≫
    (B.abelian.pullbackCompIso u a).inv = _
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  rfl

theorem levelIsoAlongAt_dual_hom (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t) :
    (levelIsoAlongAt A B u e a t w).dual.hom = AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt A.dual.abelian.scheme u a t w e.dual.hom := by
  subst t
  change (A.dual.abelian.pullbackCompIso u a).hom ≫ (Over.pullback a).map e.dual.hom ≫
    (B.dual.abelian.pullbackCompIso u a).inv = _
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  rfl

theorem levelIsoAlongAt_abelian_inv (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t) :
    (levelIsoAlongAt A B u e a t w).abelian.inv = AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt B.abelian.scheme u a t w e.abelian.inv := by
  subst t
  change ((B.abelian.pullbackCompIso u a).hom ≫ (Over.pullback a).map e.abelian.inv) ≫
    (A.abelian.pullbackCompIso u a).inv = _
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  exact Category.assoc _ _ _

theorem levelIsoAlongAt_dual_inv (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t) :
    (levelIsoAlongAt A B u e a t w).dual.inv = AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt B.dual.abelian.scheme u a t w e.dual.inv := by
  subst t
  change ((B.dual.abelian.pullbackCompIso u a).hom ≫ (Over.pullback a).map e.dual.inv) ≫
    (A.dual.abelian.pullbackCompIso u a).inv = _
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  exact Category.assoc _ _ _

theorem levelIso_base_overlap_compatible
    (hr : Subsingleton (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback (pullback.fst u u ≫ u))
      (B.pullback (pullback.fst u u ≫ u)))) :
    AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u e.abelian.hom ∧ AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u e.abelian.inv ∧
      AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u e.dual.hom ∧ AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u e.dual.inv := by
  let a := pullback.fst u u
  let b := pullback.snd u u
  let t := a ≫ u
  have he : levelIsoAlongAt A B u e a t rfl =
      levelIsoAlongAt A B u e b t pullback.condition.symm := hr.elim _ _
  refine ⟨MorphismBaseOverlap.morphism_compatible_of_base_overlap A.abelian.scheme u e.abelian.hom ?_,
    MorphismBaseOverlap.morphism_compatible_of_base_overlap B.abelian.scheme u e.abelian.inv ?_,
    MorphismBaseOverlap.morphism_compatible_of_base_overlap A.dual.abelian.scheme u e.dual.hom ?_,
    MorphismBaseOverlap.morphism_compatible_of_base_overlap B.dual.abelian.scheme u e.dual.inv ?_⟩
  · exact (levelIsoAlongAt_abelian_hom A B u e a t rfl).symm.trans
      ((congrArg (fun q => q.abelian.hom) he).trans
        (levelIsoAlongAt_abelian_hom A B u e b t pullback.condition.symm))
  · exact (levelIsoAlongAt_abelian_inv A B u e a t rfl).symm.trans
      ((congrArg (fun q => q.abelian.inv) he).trans
        (levelIsoAlongAt_abelian_inv A B u e b t pullback.condition.symm))
  · exact (levelIsoAlongAt_dual_hom A B u e a t rfl).symm.trans
      ((congrArg (fun q => q.dual.hom) he).trans
        (levelIsoAlongAt_dual_hom A B u e b t pullback.condition.symm))
  · exact (levelIsoAlongAt_dual_inv A B u e a t rfl).symm.trans
      ((congrArg (fun q => q.dual.inv) he).trans
        (levelIsoAlongAt_dual_inv A B u e b t pullback.condition.symm))

theorem levelIso_compatible_of_reduced_rigidity [IsReduced S] [IsFinite u] [Etale u]
    (hr : ∀ (V : Scheme.{0}) [IsReduced V] (t : V ⟶ S),
      Subsingleton (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (B.pullback t))) :
    AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u e.abelian.hom ∧ AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u e.abelian.inv ∧
      AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u e.dual.hom ∧ AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u e.dual.inv := by
  have : IsReduced Y := Finite.EtaleReduced.finite_etale_isReduced u
  have : IsReduced (pullback u u) := Finite.EtaleReduced.finite_etale_isReduced (pullback.fst u u)
  exact levelIso_base_overlap_compatible A B u e (hr (pullback u u) (pullback.fst u u ≫ u))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelIsoBaseOverlap
