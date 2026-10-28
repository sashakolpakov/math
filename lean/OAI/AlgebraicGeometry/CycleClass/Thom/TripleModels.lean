import OAI.AlgebraicTopology.Kunneth.ComparisonLow

/-! # Triple Models -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Three-factor singular models for the ThomClass product proof

The model in degree n is a triple of actual topological n-simplices.
Its product is contractible. The free representable presentation therefore
gives a natural homotopy between chain endomorphisms of three-factor
singular chains that agree on vertices. This is the comparison machinery
for the two parenthesizations of the existing cross product.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicTopology _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped Simplicial TensorProduct

namespace Constructions

abbrev SpaceTriple := (TopCat.{0} × TopCat.{0}) × TopCat.{0}

def tripleSpace : SpaceTriple ⥤ TopCat.{0} :=
  (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.prod (𝟭 TopCat.{0})) ⋙ AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace

variable (k : Type) [Field k]

abbrev tripleChainFunctor : SpaceTriple ⥤ ChainComplex (ModuleCat.{0} k) ℕ :=
  tripleSpace ⋙ AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k

def tripleChains : ChainComplex (SpaceTriple ⥤ ModuleCat.{0} k) ℕ where
  X n := tripleChainFunctor k ⋙ HomologicalComplex.eval _ _ n
  d i j :=
    { app X := ((tripleChainFunctor k).obj X).d i j
      naturality _ _ f := ((tripleChainFunctor k).map f).comm i j }
  shape i j hij := by
    apply NatTrans.ext
    funext X
    exact ((tripleChainFunctor k).obj X).shape i j hij
  d_comp_d' i j l _ _ := by
    apply NatTrans.ext
    funext X
    exact ((tripleChainFunctor k).obj X).d_comp_d i j l

def tripleSimplexModel (n : ℕ) : SpaceTriple :=
  ((SimplexCategory.toTop.obj ⦋n⦌, SimplexCategory.toTop.obj ⦋n⦌),
    SimplexCategory.toTop.obj ⦋n⦌)

def tripleSimplexEquiv (n : ℕ) (X : SpaceTriple) :
    (TopCat.toSSet.obj (tripleSpace.obj X)) _⦋n⦌ ≃ (tripleSimplexModel n ⟶ X) where
  toFun s :=
    ((s.down ≫ TopCat.prodFst ≫ TopCat.prodFst,
      s.down ≫ TopCat.prodFst ≫ TopCat.prodSnd), s.down ≫ TopCat.prodSnd)
  invFun f := ULift.up (TopCat.ofHom
    ⟨fun t => ((f.1.1 t, f.1.2 t), f.2 t),
      (f.1.1.hom.continuous.prodMk f.1.2.hom.continuous).prodMk f.2.hom.continuous⟩)
  left_inv s := by
    apply ULift.ext
    apply TopCat.ext
    intro t
    rfl
  right_inv f := by
    apply Prod.ext
    · apply Prod.ext <;> apply TopCat.ext <;> intro t <;> rfl
    · apply TopCat.ext
      intro t
      rfl

def tripleDegreeFreeIso (n : ℕ) (X : SpaceTriple) :
    (AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.FreeModel (k := k) (tripleSimplexModel n)).obj X ≅
      ((tripleChainFunctor k).obj X).X n where
  hom := Sigma.desc (fun f : tripleSimplexModel n ⟶ X =>
    (TopCat.toSSet.obj (tripleSpace.obj X)).ιChainComplex
      (R := ModuleCat.of k k) ((tripleSimplexEquiv n X).symm f))
  inv := Sigma.desc (fun s : (TopCat.toSSet.obj (tripleSpace.obj X)) _⦋n⦌ =>
    Sigma.ι (fun _ : tripleSimplexModel n ⟶ X => ModuleCat.of k k)
      (tripleSimplexEquiv n X s))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro f
    simp only [Sigma.ι_comp_desc_assoc, SSet.ιChainComplex,
      Sigma.ι_comp_desc, Equiv.apply_symm_apply]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    apply SSet.chainComplex_hom_ext
    intro s
    simp only [SSet.ιChainComplex, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Equiv.symm_apply_apply]
    exact (Category.comp_id _).symm

def tripleDegreeFreeNatIso (n : ℕ) :
    AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.FreeModel (k := k) (tripleSimplexModel n) ≅ (tripleChains k).X n :=
  NatIso.ofComponents (tripleDegreeFreeIso k n) (by
    intro X Y f
    apply Sigma.hom_ext
    intro s
    dsimp only [AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.FreeModel, evaluationLeftAdjoint, tripleDegreeFreeIso]
    erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    change (TopCat.toSSet.obj (tripleSpace.obj Y)).ιChainComplex
        (R := ModuleCat.of k k) ((tripleSimplexEquiv n Y).symm (s ≫ f)) =
      (TopCat.toSSet.obj (tripleSpace.obj X)).ιChainComplex
        (R := ModuleCat.of k k) ((tripleSimplexEquiv n X).symm s) ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (tripleSpace.map f))
            (ModuleCat.of k k)).f n
    erw [SSet.ι_chainComplexMap_f]
    rfl)

def triplePresentation (n : ℕ) : AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.Presentation ((tripleChains k).X n) :=
  AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.Presentation.ofSingle (tripleSimplexModel n) (tripleDegreeFreeNatIso k n)

theorem triple_model_positive_exact (m n : ℕ) :
    (((tripleChains k).sc' (n + 2) (n + 1) n).map
      ((evaluation SpaceTriple (ModuleCat.{0} k)).obj (tripleSimplexModel m))).Exact := by
  let : ContractibleSpace (SimplexCategory.toTop.{0}.obj ⦋m⦌) :=
    Geometric.SimplexFillings.Cycles.toTopSimplex_contractible m
  let X := tripleSpace.obj (tripleSimplexModel m)
  let : ContractibleSpace X := inferInstanceAs
    (ContractibleSpace (((SimplexCategory.toTop.{0}.obj ⦋m⦌) ×
      (SimplexCategory.toTop.{0}.obj ⦋m⦌)) × (SimplexCategory.toTop.{0}.obj ⦋m⦌)))
  let C := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X
  let : Subsingleton (C.homology (n + 1)) := ModuleCat.subsingleton_of_isZero
    (Geometric.ContractibleModel.Cycles.isZero_singularHomology_of_contractible (ModuleCat.of k k) X
      (n + 1) (Nat.succ_ne_zero n))
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ c : C.X (n + 1), (C.d (n + 1) n) c = 0 →
    ∃ b : C.X (n + 2), (C.d (n + 2) (n + 1)) b = c
  intro c hc
  exact (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists C (n + 1)
    ⟨c, (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ C n c).mpr hc⟩).mp (Subsingleton.elim _ _)

def tripleNaturalHomotopy
    (f g : tripleChains k ⟶ tripleChains k) (h0 : f.f 0 = g.f 0) : Homotopy f g :=
  AlgebraicTopology.Kunneth.AcyclicModelsF.Construction.AcyclicModels.homotopy (tripleChains k) (tripleChains k)
    (triplePresentation k) (fun n _ q => triple_model_positive_exact k n q) f g h0

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels
