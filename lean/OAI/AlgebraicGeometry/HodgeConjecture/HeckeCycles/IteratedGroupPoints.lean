import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeFieldPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Iterated Group Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IteratedGroupPoints.CM

noncomputable section

/-! The group-scheme associativity isomorphism for base change induces
the same point equivalence as the two pullback adjunctions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM

variable {S T : Scheme} (G : CommGrp (Over S)) {k : Type} [Field k]
  (b : T ⟶ S) (c : Spec (.of k) ⟶ T) (d : Spec (.of k) ⟶ S) (hd : c ≫ b = d)

def factorIso : (GroupBaseChange.CM.changedGroup G d).X ≅ (GroupBaseChange.CM.changedGroup (GroupBaseChange.CM.changedGroup G b) c).X :=
  (Grp.forget _).mapIso (GroupBaseChange.CM.factorGroupIso G c b d hd)

theorem compGroupIso_hom :
    ((Grp.forget _).mapIso (GroupBaseChange.CM.compGroupIso G c b)).hom = (Over.pullbackComp c b).hom.app G.X := by
  change (Over.pullbackComp c b).hom.app G.X ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem factorIso_hom_eq :
    (factorIso G b c d hd).hom =
      (eqToHom (congrArg (fun f => (Over.pullback f).obj G.X) hd.symm)) ≫
        (Over.pullbackComp c b).hom.app G.X := by
  cases hd
  change (𝟙 _) ≫ ((Grp.forget _).mapIso (GroupBaseChange.CM.compGroupIso G c b)).hom =
    (𝟙 _) ≫ (Over.pullbackComp c b).hom.app G.X
  exact congrArg (𝟙 _ ≫ ·) (compGroupIso_hom G b c)

def plainFactorIso : (GroupBaseChange.CM.changedGroup G d).X ≅ (GroupBaseChange.CM.changedGroup (GroupBaseChange.CM.changedGroup G b) c).X :=
  (eqToIso (congrArg (fun f => (Over.pullback f).obj G.X) hd)).symm ≪≫
    (Over.pullbackComp c b).app G.X

theorem factorIso_eq_plain : factorIso G b c d hd = plainFactorIso G b c d hd :=
  Iso.ext (factorIso_hom_eq G b c d hd)

theorem pullbackEq_fst {U V : Scheme} (X : Over U) (f h : V ⟶ U) (w : f = h) :
    (eqToHom (congrArg (fun z => (Over.pullback z).obj X) w)).left ≫
      pullback.fst X.hom h = pullback.fst X.hom f := by
  cases w
  exact Category.id_comp _

def factorMap : pullback G.X.hom d ⟶ pullback (pullback.snd G.X.hom b) c :=
  (factorIso G b c d hd).hom.left

theorem factorIso_hom_fst_fst :
    factorMap G b c d hd ≫ pullback.fst (pullback.snd G.X.hom b) c ≫
      pullback.fst G.X.hom b = pullback.fst G.X.hom d := by
  let r : (Over.pullback d).obj G.X ⟶ (Over.pullback (c ≫ b)).obj G.X :=
    eqToHom (congrArg (fun f => (Over.pullback f).obj G.X) hd.symm)
  let t : (Over.pullback (c ≫ b)).obj G.X ⟶
      (Over.pullback c).obj ((Over.pullback b).obj G.X) := (Over.pullbackComp c b).hom.app G.X
  have he : (factorIso G b c d hd).hom = r ≫ t := factorIso_hom_eq G b c d hd
  let r₀ : pullback G.X.hom d ⟶ pullback G.X.hom (c ≫ b) := r.left
  let t₀ : pullback G.X.hom (c ≫ b) ⟶ pullback (pullback.snd G.X.hom b) c := t.left
  have he₀ : factorMap G b c d hd = r₀ ≫ t₀ := congrArg Over.Hom.left he
  calc
    _ = (r₀ ≫ t₀) ≫ pullback.fst (pullback.snd G.X.hom b) c ≫
        pullback.fst G.X.hom b := congrArg (fun z => z ≫
          pullback.fst (pullback.snd G.X.hom b) c ≫ pullback.fst G.X.hom b) he₀
    _ = r₀ ≫ (t₀ ≫ pullback.fst (pullback.snd G.X.hom b) c ≫ pullback.fst G.X.hom b) :=
      Category.assoc _ _ _
    _ = r₀ ≫ pullback.fst G.X.hom (c ≫ b) := congrArg (r₀ ≫ ·)
      (AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst G.X b c)
    _ = pullback.fst G.X.hom d := pullbackEq_fst G.X d (c ≫ b) hd.symm

theorem factorIso_points (p : Geometric.PointExt.CM.pointBase k ⟶ (GroupBaseChange.CM.changedGroup G d).X) :
    FiberGeneration.CM.fiberPointsEquiv (GroupBaseChange.CM.changedGroup G b).X c (p ≫ (factorIso G b c d hd).hom) =
      PrimeFieldPoints.CM.pointEquiv b c d hd G.X p := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hp := PrimeFieldPoints.CM.pointEquiv_projection b c d hd G.X p
    have hf := congrArg (p.left ≫ ·) (factorIso_hom_fst_fst G b c d hd)
    change (𝟙 _ ≫ ((p.left ≫ (factorIso G b c d hd).hom.left) ≫
        pullback.fst (pullback.snd G.X.hom b) c)) ≫ pullback.fst G.X.hom b = _
    have hh : (𝟙 _ ≫ ((p.left ≫ (factorIso G b c d hd).hom.left) ≫
        pullback.fst (pullback.snd G.X.hom b) c)) ≫ pullback.fst G.X.hom b =
      p.left ≫ pullback.fst G.X.hom d := by
      erw [Category.id_comp, Category.assoc, Category.assoc]
      exact hf
    exact hh.trans hp.symm
  · exact (FiberGeneration.CM.fiberPointsEquiv (GroupBaseChange.CM.changedGroup G b).X c
      (p ≫ (factorIso G b c d hd).hom)).w.trans
        (PrimeFieldPoints.CM.pointEquiv b c d hd G.X p).w.symm

theorem plainFactorIso_points (p : Geometric.PointExt.CM.pointBase k ⟶ (GroupBaseChange.CM.changedGroup G d).X) :
    FiberGeneration.CM.fiberPointsEquiv (GroupBaseChange.CM.changedGroup G b).X c (p ≫ (plainFactorIso G b c d hd).hom) =
      PrimeFieldPoints.CM.pointEquiv b c d hd G.X p := by
  rw [← factorIso_eq_plain]
  exact factorIso_points G b c d hd p

theorem plainFactorIso_group : IsMonHom (plainFactorIso G b c d hd).hom := by
  rw [← factorIso_eq_plain]
  exact (GroupBaseChange.CM.factorGroupIso G c b d hd).hom.hom.isMonHom_hom

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IteratedGroupPoints.CM
