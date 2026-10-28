import OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.Homotopy

/-! # Subdivision Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles

noncomputable section

/-!
# Natural singular-chain fillings for subdivision homotopies

The ordinary singular chains form a chain complex in the functor category
`TopCat ⥤ ModuleCat ℤ`. Its degree-n functor is represented by the actual
topological n-simplex, in the free-module sense expressed by mathlib's
singular-chain adjunction. Positive cycles on this model have genuine fillings.
These facts permit natural chain-homotopy induction, without postulating
acyclic models or a subdivision homotopy.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The degree-n ordinary integral singular chain functor. -/
abbrev singularChainDegreeFunctor (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  LocalHomology.Cycles.integralSingularChainFunctor ⋙
    HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n

/-- The actual singular boundary is natural in the topological space. -/
def singularBoundaryNatural (i j : ℕ) :
    singularChainDegreeFunctor i ⟶ singularChainDegreeFunctor j where
  app X := (LocalHomology.Cycles.integralSingularChains X).d i j
  naturality _ _ f := (LocalHomology.Cycles.integralSingularChainFunctor.map f).comm i j

/-- Genuine integral singular chains viewed as a complex of functors. -/
abbrev naturalSingularChains : ChainComplex (TopCat.{0} ⥤ ModuleCat.{0} ℤ) ℕ where
  X := singularChainDegreeFunctor
  d := singularBoundaryNatural
  shape i j h := by
    apply NatTrans.ext
    funext X
    exact (LocalHomology.Cycles.integralSingularChains X).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext X
    exact (LocalHomology.Cycles.integralSingularChains X).d_comp_d i j k

/-- A natural degree-n chain operation is evaluated on its genuine simplex model. -/
def singularModelEvaluation (n k : ℕ)
    (a : singularChainDegreeFunctor n ⟶ singularChainDegreeFunctor k) :
    ModuleCat.of ℤ ℤ ⟶
      (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋n⦌)).X k :=
  (singularChainComplexFunctorAdjunction (ModuleCat.{0} ℤ) n).homEquiv
    (ModuleCat.of ℤ ℤ) (singularChainDegreeFunctor k) a

/-- Evaluation on the universal simplex detects equality of natural operations. -/
theorem singularModelEvaluation_injective (n k : ℕ) :
    Function.Injective (singularModelEvaluation n k) :=
  (singularChainComplexFunctorAdjunction (ModuleCat.{0} ℤ) n).homEquiv
    (ModuleCat.of ℤ ℤ) (singularChainDegreeFunctor k) |>.injective

@[simp]
theorem singularModelEvaluation_zero (n k : ℕ) :
    singularModelEvaluation n k 0 = 0 := by
  simp [singularModelEvaluation]; rfl

/-- Model evaluation commutes with a further natural chain operation. -/
theorem singularModelEvaluation_comp (n k l : ℕ)
    (a : singularChainDegreeFunctor n ⟶ singularChainDegreeFunctor k)
    (b : singularChainDegreeFunctor k ⟶ singularChainDegreeFunctor l) :
    singularModelEvaluation n l (a ≫ b) =
      singularModelEvaluation n k a ≫ b.app (SimplexCategory.toTop.{0}.obj ⦋n⦌) :=
  (singularChainComplexFunctorAdjunction (ModuleCat.{0} ℤ) n).homEquiv_naturality_right a b

/-- Every natural positive-cycle operation admits a natural filling operation.
The filling is obtained from the proved contractibility of the actual standard
simplex, then extended by its free singular-chain universal property. -/
theorem exists_naturalSingularFilling (n k : ℕ)
    (a : singularChainDegreeFunctor n ⟶ singularChainDegreeFunctor (k + 1))
    (ha : a ≫ singularBoundaryNatural (k + 1) k = 0) :
    ∃ b : singularChainDegreeFunctor n ⟶ singularChainDegreeFunctor (k + 2),
      b ≫ singularBoundaryNatural (k + 2) (k + 1) = a := by
  let model := SimplexCategory.toTop.{0}.obj ⦋n⦌
  let v := singularModelEvaluation n (k + 1) a
  have hv : v ≫ (LocalHomology.Cycles.integralSingularChains model).d (k + 1) k = 0 := by
    change singularModelEvaluation n (k + 1) a ≫
      (singularBoundaryNatural (k + 1) k).app model = 0
    rw [← singularModelEvaluation_comp, ha, singularModelEvaluation_zero]
  have hcycle : (LocalHomology.Cycles.integralSingularChains model).d (k + 1) k (v 1) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply] using!
      congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ (LocalHomology.Cycles.integralSingularChains model).X k ↦ f.hom 1) hv
  obtain ⟨c, hc⟩ := SimplexFillings.Cycles.exists_simplex_boundary_succ n k (v 1) hcycle
  let cf : ModuleCat.of ℤ ℤ ⟶ (LocalHomology.Cycles.integralSingularChains model).X (k + 2) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ c)
  have hcf : cf.hom 1 = c := LinearMap.toSpanSingleton_apply_one ℤ _ c
  let b := ((singularChainComplexFunctorAdjunction (ModuleCat.{0} ℤ) n).homEquiv
    (ModuleCat.of ℤ ℤ) (singularChainDegreeFunctor (k + 2))).symm cf
  refine ⟨b, ?_⟩
  apply singularModelEvaluation_injective n (k + 1)
  rw [singularModelEvaluation_comp]
  have hb : singularModelEvaluation n (k + 2) b = cf :=
    Equiv.apply_symm_apply _ _
  rw [hb]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (cf ≫ (LocalHomology.Cycles.integralSingularChains model).d (k + 2) (k + 1)).hom 1 = v.hom 1
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, hcf]
  exact hc

/-- A natural singular-chain endomorphism which vanishes in degree zero is
naturally null-homotopic. This is the acyclic-model argument proved from the
actual simplex fillings, rather than an assumed acyclic-model principle. -/
def naturalSingularNullhomotopy (e : naturalSingularChains ⟶ naturalSingularChains)
    (he : e.f 0 = 0) : Homotopy e 0 := by
  classical
  have hclosed : e.f 1 ≫ singularBoundaryNatural 1 0 = 0 := by
    change e.f 1 ≫ naturalSingularChains.d 1 0 = 0
    rw [e.comm 1 0, he, comp_zero]
  let hfirst := exists_naturalSingularFilling 1 0 (e.f 1) hclosed
  let first := Classical.choose hfirst
  have hfirst_eq := Classical.choose_spec hfirst
  refine Homotopy.mkInductive e 0 ?_ first ?_ ?_
  · simpa only [zero_comp] using he
  · simpa only [first, comp_zero, zero_add] using! hfirst_eq.symm
  · intro n p
    rcases p with ⟨u, v, hp⟩
    let a := e.f (n + 2) - naturalSingularChains.d (n + 2) (n + 1) ≫ v
    have ha : a ≫ singularBoundaryNatural (n + 2) (n + 1) = 0 := by
      change a ≫ naturalSingularChains.d (n + 2) (n + 1) = 0
      dsimp only [a]
      rw [Preadditive.sub_comp, e.comm (n + 2) (n + 1), hp,
        Preadditive.comp_add]
      simp only [← Category.assoc, naturalSingularChains.d_comp_d,
        zero_comp, zero_add, sub_self]
    let hnext := exists_naturalSingularFilling (n + 2) (n + 1) a ha
    refine ⟨Classical.choose hnext, ?_⟩
    have hnext_eq := Classical.choose_spec hnext
    change e.f (n + 2) = naturalSingularChains.d (n + 2) (n + 1) ≫ v +
      Classical.choose hnext ≫ singularBoundaryNatural (n + 3) (n + 2)
    rw [hnext_eq]
    dsimp only [a]
    abel

/-- Natural chain endomorphisms agreeing in degree zero are naturally
chain-homotopic, by applying the proved natural filling induction to their difference. -/
def naturalSingularHomotopy (f g : naturalSingularChains ⟶ naturalSingularChains)
    (hzero : f.f 0 = g.f 0) : Homotopy f g :=
  (Homotopy.equivSubZero (f := f) (g := g)).symm (naturalSingularNullhomotopy (f - g) (by
    change f.f 0 - g.f 0 = 0
    rw [hzero, sub_self]))

/-- The signed geometric subdivision chain map, simultaneously on all spaces. -/
def naturalSubdivision : naturalSingularChains ⟶ naturalSingularChains where
  f n :=
    { app X := (SubdivisionBoundary.Cycles.subdivisionChainMap X).f n
      naturality X Y f := by
        apply ModuleCat.hom_ext
        simpa only [ModuleCat.hom_comp, SubdivisionBoundary.Cycles.subdivisionChainMap_f] using!
          (SubdivisionNaturality.Cycles.subdivisionDegree_naturality f n).symm }
  comm' i j _ := by
    apply NatTrans.ext
    funext X
    exact (SubdivisionBoundary.Cycles.subdivisionChainMap X).comm i j

/-- The actual subdivision natural transformation is the identity in degree zero. -/
theorem naturalSubdivision_zero :
    naturalSubdivision.f 0 = 𝟙 (singularChainDegreeFunctor 0) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  change ((SubdivisionBoundary.Cycles.subdivisionChainMap X).f 0).hom = LinearMap.id
  rw [SubdivisionBoundary.Cycles.subdivisionChainMap_f, SubdivisionNaturality.Cycles.subdivisionDegree_zero_dimension]

/-- The genuine subdivision chain homotopy, constructed by natural simplex fillings. -/
def naturalSubdivisionHomotopy : Homotopy naturalSubdivision (𝟙 naturalSingularChains) :=
  naturalSingularHomotopy naturalSubdivision (𝟙 naturalSingularChains) naturalSubdivision_zero

/-- Evaluation of a natural singular-chain map on an actual topological space. -/
def naturalSingularChainMapAt (e : naturalSingularChains ⟶ naturalSingularChains)
    (X : TopCat.{0}) : LocalHomology.Cycles.integralSingularChains X ⟶ LocalHomology.Cycles.integralSingularChains X where
  f i := (e.f i).app X
  comm' i j _ := NatTrans.congr_app (e.comm i j) X

/-- Evaluation of a natural chain homotopy on an actual space. -/
def naturalSingularHomotopyAt
    {f g : naturalSingularChains ⟶ naturalSingularChains} (h : Homotopy f g)
    (X : TopCat.{0}) :
    Homotopy (naturalSingularChainMapAt f X) (naturalSingularChainMapAt g X) where
  hom i j := (h.hom i j).app X
  zero i j hij := NatTrans.congr_app (h.zero i j hij) X
  comm i := NatTrans.congr_app (h.comm i) X

/-- Actual barycentric subdivision is chain-homotopic to the identity. -/
def subdivisionHomotopy (X : TopCat.{0}) :
    Homotopy (SubdivisionBoundary.Cycles.subdivisionChainMap X) (𝟙 (LocalHomology.Cycles.integralSingularChains X)) :=
  naturalSingularHomotopyAt naturalSubdivisionHomotopy X

/-- The constructed subdivision homotopy is natural under continuous maps. -/
theorem subdivisionHomotopy_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (i j : ℕ) :
    (LocalHomology.Cycles.integralSingularChainFunctor.map f).f i ≫ (subdivisionHomotopy Y).hom i j =
      (subdivisionHomotopy X).hom i j ≫ (LocalHomology.Cycles.integralSingularChainFunctor.map f).f j :=
  (naturalSubdivisionHomotopy.hom i j).naturality f

/-- In particular the actual homotopy preserves chains coming from every subspace. -/
theorem subdivisionHomotopy_subspace (X : TopCat.{0}) (A : Set X) (i j : ℕ) :
    (LocalHomology.Cycles.subspaceChainInclusion X A).f i ≫ (subdivisionHomotopy X).hom i j =
      (subdivisionHomotopy (TopCat.of A)).hom i j ≫ (LocalHomology.Cycles.subspaceChainInclusion X A).f j :=
  subdivisionHomotopy_naturality (LocalHomology.Cycles.subspaceInclusion X A) i j

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles
