import OAI.AlgebraicTopology.Kunneth.ProductModelsAs

/-! # Models -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Models

noncomputable section

/-!
# ChernClass: natural chain homotopies from genuine singular-simplex models

The singular-chain functor is free on each actual standard simplex.
Contractibility of these models gives uniqueness up to natural chain
homotopy for endomorphisms agreeing on vertices.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

def chainsAsNaturalComplex (F : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} k) ℕ) :
    ChainComplex (TopCat.{0} ⥤ ModuleCat.{0} k) ℕ where
  X n := F ⋙ HomologicalComplex.eval _ _ n
  d i j := { app X := (F.obj X).d i j
             naturality _ _ f := (F.map f).comm i j }
  shape i j hij := by
    apply NatTrans.ext
    funext X
    exact (F.obj X).shape i j hij
  d_comp_d' i j l _ _ := by
    apply NatTrans.ext
    funext X
    exact (F.obj X).d_comp_d i j l

abbrev singularNaturalChains := chainsAsNaturalComplex k (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k)

def singularModelFreeIso (n : ℕ) (X : TopCat.{0}) :
    (AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.FreeModel (k := k) (SimplexCategory.toTop.obj ⦋n⦌)).obj X ≅
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X n where
  hom := Sigma.desc (fun f : SimplexCategory.toTop.obj ⦋n⦌ ⟶ X =>
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) (ULift.up f))
  inv := Sigma.desc (fun s : (TopCat.toSSet.obj X) _⦋n⦌ =>
    Sigma.ι (fun _ : SimplexCategory.toTop.obj ⦋n⦌ ⟶ X => ModuleCat.of k k) s.down)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro f
    simp only [Sigma.ι_comp_desc_assoc, SSet.ιChainComplex, Sigma.ι_comp_desc]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    apply SSet.chainComplex_hom_ext
    intro s
    simp only [SSet.ιChainComplex, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact (Category.comp_id _).symm

def singularModelFreeNatIso (n : ℕ) :
    AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.FreeModel (k := k) (SimplexCategory.toTop.obj ⦋n⦌) ≅
      (singularNaturalChains k).X n :=
  NatIso.ofComponents (singularModelFreeIso k n) (by
    intro X Y f
    apply Sigma.hom_ext
    intro s
    dsimp only [AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.FreeModel, evaluationLeftAdjoint, singularModelFreeIso]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    change (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of k k) (ULift.up (s ≫ f)) =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) (ULift.up s) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of k k)).f n
    erw [SSet.ι_chainComplexMap_f]
    rfl)

def singularModels (n : ℕ) : AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.Presentation ((singularNaturalChains k).X n) :=
  AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.Presentation.ofSingle (SimplexCategory.toTop.obj ⦋n⦌)
    (singularModelFreeNatIso k n)

theorem singularModel_positive_exact (m n : ℕ) :
    (((singularNaturalChains k).sc' (n + 2) (n + 1) n).map
      ((evaluation TopCat.{0} (ModuleCat.{0} k)).obj
        (SimplexCategory.toTop.obj ⦋m⦌))).Exact := by
  let X := SimplexCategory.toTop.{0}.obj ⦋m⦌
  let : ContractibleSpace X := CycleClass.Geometric.SimplexFillings.Cycles.toTopSimplex_contractible m
  let C := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X
  let : Subsingleton (C.homology (n + 1)) := ModuleCat.subsingleton_of_isZero
    (CycleClass.Geometric.ContractibleModel.Cycles.isZero_singularHomology_of_contractible (ModuleCat.of k k) X
      (n + 1) (Nat.succ_ne_zero n))
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ c : C.X (n + 1), (C.d (n + 1) n) c = 0 →
    ∃ b : C.X (n + 2), (C.d (n + 2) (n + 1)) b = c
  intro c hc
  exact (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists C (n + 1)
    ⟨c, (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ C n c).mpr hc⟩).mp (Subsingleton.elim _ _)

def singularNaturalHomotopy (f g : singularNaturalChains k ⟶ singularNaturalChains k)
    (h0 : f.f 0 = g.f 0) : Homotopy f g :=
  AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.homotopy (singularNaturalChains k) (singularNaturalChains k)
    (singularModels k) (fun n _ q => singularModel_positive_exact k n q) f g h0

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Models
