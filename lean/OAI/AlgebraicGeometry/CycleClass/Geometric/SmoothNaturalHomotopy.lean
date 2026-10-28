import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSimplexModels
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSimplexFillings
import Mathlib.Algebra.Homology.Homotopy

/-! # Smooth Natural Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Natural smooth-chain homotopies from actual smooth model fillings

An operation on smooth singular chains is determined by its value on the
identity simplex of each closed standard-simplex model. Conversely, a chain
on that model is transported by the genuine simplex maps and extended by the
free-module universal property. The proved smooth model fillings therefore
give natural chain homotopies, entirely inside the smooth singular complexes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Maps of these spaces carry each actual simplex generator to its image. -/
@[reassoc (attr := simp)]
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap_generator {X Y : SmoothSimplexModels.Cycles.SmoothSimplexSpace} (f : X ⟶ Y) (n : ℕ)
    (σ : X.smooth.toSSet.obj (.op ⦋n⦌)) :
    X.smooth.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f n =
      Y.smooth.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.mapSmooth f).app (.op ⦋n⦌) σ) :=
  SSet.ι_chainComplexMap_f _ _ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.mapSmooth f) (ModuleCat.of ℤ ℤ) σ

/-- Evaluation of a natural operation on the actual identity model simplex. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation (n k : ℕ) (a : SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor n ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor k) :
    ModuleCat.of ℤ ℤ ⟶ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).X k :=
  (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n).smooth.toSSet.ιChainComplex (SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelSimplex n) ≫ a.app (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)

@[simp]
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_zero (n k : ℕ) : SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation n k 0 = 0 := by
  simp [SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation]

theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_comp (n k l : ℕ)
    (a : SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor n ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor k)
    (b : SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor k ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor l) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation n l (a ≫ b) = SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation n k a ≫ b.app (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n) := by
  simp only [SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation, NatTrans.comp_app, Category.assoc]

/-- Naturality expresses the operation on every generator in terms of the
closed-simplex model value. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_generator (n k : ℕ)
    (a : SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor n ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor k) (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace)
    (σ : X.smooth.toSSet.obj (.op ⦋n⦌)) :
    X.smooth.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ a.app X =
      SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation n k a ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap (SmoothSimplexModels.Cycles.SmoothSimplexSpace.fromSimplex X n σ)).f k := by
  rw [← SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelGenerator_chainMap X n σ, Category.assoc]
  change _ ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor n).map (SmoothSimplexModels.Cycles.SmoothSimplexSpace.fromSimplex X n σ) ≫ a.app X = _
  rw [a.naturality]
  rfl

/-- Model evaluation detects equality of natural smooth-chain operations. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_injective (n k : ℕ) :
    Function.Injective (SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation n k) := by
  intro a b hab
  apply NatTrans.ext
  funext X
  apply SSet.chainComplex_hom_ext
  intro σ
  change X.smooth.toSSet.ιChainComplex σ ≫ a.app X =
    X.smooth.toSSet.ιChainComplex σ ≫ b.app X
  rw [SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_generator, SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_generator, hab]

/-- Extend a model chain operation along every actual smooth simplex. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.extendModelOperation (n k : ℕ)
    (c : ModuleCat.of ℤ ℤ ⟶ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).X k) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor n ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor k where
  app X := Sigma.desc (fun σ : X.smooth.toSSet.obj (.op ⦋n⦌) =>
    c ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap (SmoothSimplexModels.Cycles.SmoothSimplexSpace.fromSimplex X n σ)).f k)
  naturality X Y f := by
    apply SSet.chainComplex_hom_ext
    intro σ
    change X.smooth.toSSet.ιChainComplex σ ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f n ≫ Sigma.desc _ =
      X.smooth.toSSet.ιChainComplex σ ≫ Sigma.desc _ ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f k
    rw [← Category.assoc, SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap_generator]
    change Y.smooth.toSSet.ιChainComplex ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.mapSmooth f).app (.op ⦋n⦌) σ) ≫
        Sigma.desc _ = X.smooth.toSSet.ιChainComplex σ ≫ Sigma.desc _ ≫ _
    simp only [SSet.ιChainComplex, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    rw [← SmoothSimplexModels.Cycles.SmoothSimplexSpace.fromSimplex_naturality]
    change c ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainFunctor.map (SmoothSimplexModels.Cycles.SmoothSimplexSpace.fromSimplex X n σ ≫ f)).f k = _
    rw [Functor.map_comp]
    rfl

/-- The extension has precisely its defining generator value. -/
@[reassoc (attr := simp)]
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.extendModelOperation_generator (n k : ℕ)
    (c : ModuleCat.of ℤ ℤ ⟶ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).X k) (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace)
    (σ : X.smooth.toSSet.obj (.op ⦋n⦌)) :
    X.smooth.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
        (SmoothSimplexModels.Cycles.SmoothSimplexSpace.extendModelOperation n k c).app X =
      c ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap (SmoothSimplexModels.Cycles.SmoothSimplexSpace.fromSimplex X n σ)).f k := by
  exact Sigma.ι_comp_desc _ _

@[simp]
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_extendModelOperation (n k : ℕ)
    (c : ModuleCat.of ℤ ℤ ⟶ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).X k) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation n k (SmoothSimplexModels.Cycles.SmoothSimplexSpace.extendModelOperation n k c) = c := by
  rw [SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation, SmoothSimplexModels.Cycles.SmoothSimplexSpace.extendModelOperation_generator, SmoothSimplexModels.Cycles.SmoothSimplexSpace.fromSimplex_modelSimplex_id]
  simp [SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap]

/-- A natural positive-cycle operation has a natural filling consisting of
actual smooth singular chains. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.exists_naturalSmoothFilling (n k : ℕ)
    (a : SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor n ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor (k + 1))
    (ha : a ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.boundaryNatural (k + 1) k = 0) :
    ∃ b : SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor n ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor (k + 2),
      b ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.boundaryNatural (k + 2) (k + 1) = a := by
  let v := SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation n (k + 1) a
  have hv : v ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).d (k + 1) k = 0 := by
    change SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation n (k + 1) a ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.boundaryNatural (k + 1) k).app (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n) = 0
    rw [← SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_comp, ha, SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_zero]
  have hcycle : (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).d (k + 1) k (v 1) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply] using
      congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).X k => f.hom 1) hv
  obtain ⟨c, hc⟩ := SmoothSimplexFillings.Cycles.exists_smoothSimplexModel_boundary_succ n k (v 1) hcycle
  let cf : ModuleCat.of ℤ ℤ ⟶ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).X (k + 2) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ c)
  have hcf : cf.hom 1 = c := LinearMap.toSpanSingleton_apply_one ℤ _ c
  refine ⟨SmoothSimplexModels.Cycles.SmoothSimplexSpace.extendModelOperation n (k + 2) cf, ?_⟩
  apply SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_injective n (k + 1)
  rw [SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_comp, SmoothSimplexModels.Cycles.SmoothSimplexSpace.modelEvaluation_extendModelOperation]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (cf ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.model n)).d (k + 2) (k + 1)).hom 1 = v.hom 1
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, hcf]
  exact hc

/-- A natural smooth-chain endomorphism zero in degree zero is naturally
null-homotopic through the proved smooth simplex model fillings. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalNullhomotopy (e : SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains) (he : e.f 0 = 0) :
    Homotopy e 0 := by
  classical
  have hclosed : e.f 1 ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.boundaryNatural 1 0 = 0 := by
    change e.f 1 ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains.d 1 0 = 0
    rw [e.comm 1 0, he, comp_zero]
  let hfirst := SmoothSimplexModels.Cycles.SmoothSimplexSpace.exists_naturalSmoothFilling 1 0 (e.f 1) hclosed
  let first := Classical.choose hfirst
  have hfirst_eq := Classical.choose_spec hfirst
  refine Homotopy.mkInductive e 0 ?_ first ?_ ?_
  · simpa only [zero_comp] using he
  · simpa only [first, comp_zero, zero_add] using hfirst_eq.symm
  · intro n p
    rcases p with ⟨u, v, hp⟩
    let a := e.f (n + 2) - SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains.d (n + 2) (n + 1) ≫ v
    have ha : a ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.boundaryNatural (n + 2) (n + 1) = 0 := by
      change a ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains.d (n + 2) (n + 1) = 0
      dsimp only [a]
      rw [Preadditive.sub_comp, e.comm (n + 2) (n + 1), hp,
        Preadditive.comp_add]
      simp only [← Category.assoc, SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains.d_comp_d,
        zero_comp, zero_add, sub_self]
    let hnext := SmoothSimplexModels.Cycles.SmoothSimplexSpace.exists_naturalSmoothFilling (n + 2) (n + 1) a ha
    refine ⟨Classical.choose hnext, ?_⟩
    have hnext_eq := Classical.choose_spec hnext
    change e.f (n + 2) = SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains.d (n + 2) (n + 1) ≫ v +
      Classical.choose hnext ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.boundaryNatural (n + 3) (n + 2)
    rw [hnext_eq]
    dsimp only [a]
    abel

/-- Natural smooth-chain endomorphisms agreeing in degree zero are naturally
homotopic without leaving the actual smooth chain functor. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalHomotopy (f g : SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains)
    (hzero : f.f 0 = g.f 0) : Homotopy f g :=
  (Homotopy.equivSubZero (f := f) (g := g)).symm (SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalNullhomotopy (f - g) (by
    change f.f 0 - g.f 0 = 0
    rw [hzero, sub_self]))

/-- Evaluate a natural chain map at an actual smooth singular space. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMapAt (e : SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains) (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X where
  f i := (e.f i).app X
  comm' i j _ := NatTrans.congr_app (e.comm i j) X

/-- Evaluate the natural homotopy in the actual smooth chain complex. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.homotopyAt {f g : SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains} (h : Homotopy f g)
    (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) : Homotopy (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMapAt f X) (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMapAt g X) where
  hom i j := (h.hom i j).app X
  zero i j hij := NatTrans.congr_app (h.zero i j hij) X
  comm i := NatTrans.congr_app (h.comm i) X

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
