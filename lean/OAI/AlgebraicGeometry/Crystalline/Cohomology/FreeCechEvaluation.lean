import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechGenerators

/-! # Free Cech Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechEvaluation.CrystallineFreeCechEvaluation

noncomputable section

/-!
# Evaluated native free Čech chains and fibrewise tuple chains

Evaluation commutes with the outer coproduct of free representables.
Flattening the two coproducts identifies its generators with native
intersection arrows. Their checked naturality gives a simplicial
isomorphism, and hence an isomorphism of the actual chain complexes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial _root_.AlgebraicTopology

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q T : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring) (M : SheafInjectives.CrystallineSheafInjectives.Modules p k)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

def evaluated : SimplicialObject V :=
  FreeCech.CrystallineFreeCech.simplicial p k X Q s M ⋙ (CategoryTheory.evaluation _ V).obj (op T)

def copowers : SimplicialObject V :=
  CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.simplicial p k X Q T s ⋙ sigmaConst.obj M

def component (n : SimplexCategoryᵒᵖ) :
    (evaluated p k X Q T s M).obj n ≅ (copowers p k X Q T s M).obj n :=
  FreeCech.CrystallineFreeCech.evaluationIso p k X Q s M T n.unop.len ≪≫
    sigmaSigmaIso
      (fun t : ((N).obj n).I => T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj n).obj t))
      (fun _ _ => M)

theorem generator_inv (n : SimplexCategoryᵒᵖ)
    (z : CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.Arrows p k X Q T s n) :
    Sigma.ι (fun (_ : CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.Arrows p k X Q T s n) => M) z ≫
        (component p k X Q T s M n).inv =
      FreeCechGenerators.CrystallineFreeCechGenerators.generator p k X Q T s M n z := by
  let H := fun t : ((N).obj n).I => T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj n).obj t)
  let G := (CategoryTheory.evaluation _ V).obj (op T)
  let D := FreeCechGenerators.CrystallineFreeCechGenerators.family p k X Q s M n
  have h₁ : Sigma.ι (fun (_ : Σ t, H t) => M) z ≫
      (sigmaSigmaIso H (fun _ _ => M)).inv =
        Sigma.ι (fun (_ : H z.1) => M) z.2 ≫ Sigma.ι (fun t => ∐ (fun (_ : H t) => M)) z.1 :=
    Sigma.ι_comp_desc (fun a : Σ t, H t =>
      Sigma.ι (fun (_ : H a.1) => M) a.2 ≫ Sigma.ι (fun t => ∐ (fun (_ : H t) => M)) a.1) z
  have h₂ := ι_comp_sigmaComparison G D z.1
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (PreservesCoproduct.iso G D).inv) h₁).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun a => Sigma.ι (fun (_ : H z.1) => M) z.2 ≫ a) h₂)))

theorem inverse_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (component p k X Q T s M n).inv ≫ (evaluated p k X Q T s M).map f =
      (copowers p k X Q T s M).map f ≫ (component p k X Q T s M m).inv := by
  apply Sigma.hom_ext
  intro z
  have hn := generator_inv p k X Q T s M n z
  have hm := generator_inv p k X Q T s M m (CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.map p k X Q T s f z)
  have hg := FreeCechGenerators.CrystallineFreeCechGenerators.naturality p k X Q T s M f z
  have hs : Sigma.ι (fun (_ : CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.Arrows p k X Q T s n) => M) z ≫
      (copowers p k X Q T s M).map f =
        Sigma.ι (fun (_ : CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.Arrows p k X Q T s m) => M)
          (CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.map p k X Q T s f z) :=
    (Sigma.ι_comp_map'
      (f := fun (_ : CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.Arrows p k X Q T s m) => M)
      (g := fun (_ : CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.Arrows p k X Q T s n) => M)
      (CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.map p k X Q T s f) (fun _ => 𝟙 M) z).trans
        (Category.id_comp _)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (evaluated p k X Q T s M).map f) hn).trans
      (hg.trans (hm.symm.trans
        ((congrArg (fun a => a ≫ (component p k X Q T s M m).inv) hs).symm.trans
          (Category.assoc _ _ _)))))

def simplicialIso : evaluated p k X Q T s M ≅ copowers p k X Q T s M :=
  (NatIso.ofComponents (fun n => (component p k X Q T s M n).symm)
    (fun {_ _} f => (inverse_naturality p k X Q T s M f).symm)).symm

def tupleIso : evaluated p k X Q T s M ≅
    (FiberTuple.FiberTupleCech.coefficients (CrystallineCech.ArrowTuples.CrystallineCechArrowTuples.LiftIndex p k X Q T s) V M).left :=
  simplicialIso p k X Q T s M ≪≫
    Functor.isoWhiskerRight (CrystallineCech.ArrowSimplicial.CrystallineCechArrowSimplicial.iso p k X Q T s) (sigmaConst.obj M)

def chainIso :
    (((CategoryTheory.evaluation _ V).obj (op T)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (FreeCech.CrystallineFreeCech.complex p k X Q s M) ≅
        FiberTuple.FiberTupleCech.complex (CrystallineCech.ArrowTuples.CrystallineCechArrowTuples.LiftIndex p k X Q T s) V M :=
  eqToIso (congrArg (fun F => F.obj (FreeCech.CrystallineFreeCech.simplicial p k X Q s M))
    (map_alternatingFaceMapComplex ((CategoryTheory.evaluation _ V).obj (op T)))) ≪≫
      (alternatingFaceMapComplex V).mapIso (tupleIso p k X Q T s M)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechEvaluation.CrystallineFreeCechEvaluation
