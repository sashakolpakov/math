import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge

/-! # Ordered Cech Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechCoefficientNaturality

noncomputable section

/-! The actual supported ordered Cech edge is natural in the coefficient
complex, including the endomorphisms that express fixedness. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_square {A : Type*} [Category A]
    {S₁ S₂ T₁ T₂ C₁ C₂ : A}
    (s : S₁ ⟶ S₂) (i₁ : S₁ ⟶ T₁) (i₂ : S₂ ⟶ T₂) (d : T₁ ⟶ T₂)
    (e₁ : C₁ ≅ T₁) (e₂ : C₂ ≅ T₂) (c : C₁ ⟶ C₂)
    (h₁ : s ≫ i₂ = i₁ ≫ d) (h₂ : c ≫ e₂.hom = e₁.hom ≫ d) :
    s ≫ (i₂ ≫ e₂.inv) = (i₁ ≫ e₁.inv) ≫ c := by
  apply (cancel_mono e₂.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₂, ← Category.assoc e₁.inv e₁.hom d, e₁.inv_hom_id, Category.id_comp]
  exact h₁

universe u v w z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type w} [LinearOrder ι] (U : ι → C) (O : Opens X)
  {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v w z} R)) ℕ} (a : K ⟶ L)

local instance coefficient_limits [UnivLE.{w,z}] : HasLimitsOfSize.{w,w} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{w,w,z,u}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) :=
  ModuleCat.hasColimitsOfSize.{z,u,0,0} R

def sourceMap := ((OrderedCechEdge.supportFunctor.{u,v,w,z} R X F O).mapHomologicalComplex (.up ℕ)).map a

def presheafMap := ((OrderedCechEdge.presheaves.{u,v,w,z} R X F).mapHomologicalComplex (.up ℕ)).map a

def bicomplexMap : OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K ⟶
    OrderedCechEdge.bicomplex.{u,v,w,z} R X F U L :=
  ((AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map
    (presheafMap.{u,v,w,z} R X F a)

local instance total_exists (M : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v w z} R)) ℕ) :
    (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U M).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def totalMap := HomologicalComplex₂.total.map (bicomplexMap.{u,v,w,z} R X F U a) (.up ℕ)

theorem component (q : ℕ) :
    (sourceMap.{u,v,w,z} R X F O a).f q ≫ OrderedCechEdge.component.{u,v,w,z} R X F U O L q =
      OrderedCechEdge.component.{u,v,w,z} R X F U O K q ≫
        ((bicomplexMap.{u,v,w,z} R X F U a).f q).f 0 := by
  have h₁ := (SectionsExcision.inclusion
    (F.obj (⊤_ C)) (F.obj (⊤_ C) ⊓ O) inf_le_left).naturality (a.f q)
  have h₂ := AugmentedOrdered.CechZero.zeroIso_naturality U
    (F.op ⋙ (K.X q).obj) (Functor.whiskerLeft F.op (a.f q).hom)
  exact inverse_square _ _ _ _ _ _ _ h₁ h₂

variable (hO : ∀ i, F.obj (U i) ≤ O)

theorem edge :
    OrderedCechEdge.map.{u,v,w,z} R X F U O K hO ≫ totalMap.{u,v,w,z} R X F U a =
      sourceMap.{u,v,w,z} R X F O a ≫ OrderedCechEdge.map.{u,v,w,z} R X F U O L hO :=
  BicomplexHorizontalEdge.naturality _ _ _ _ _ _ _ _ _ _
    (bicomplexMap.{u,v,w,z} R X F U a) (sourceMap.{u,v,w,z} R X F O a)
    (fun q => (component.{u,v,w,z} R X F U O a q).symm)

theorem homology (n : ℕ) :
    HomologicalComplex.homologyMap (OrderedCechEdge.map.{u,v,w,z} R X F U O K hO) n ≫
        HomologicalComplex.homologyMap (totalMap.{u,v,w,z} R X F U a) n =
      HomologicalComplex.homologyMap (sourceMap.{u,v,w,z} R X F O a) n ≫
        HomologicalComplex.homologyMap (OrderedCechEdge.map.{u,v,w,z} R X F U O L hO) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f n) (edge.{u,v,w,z} R X F U O a hO)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechCoefficientNaturality
