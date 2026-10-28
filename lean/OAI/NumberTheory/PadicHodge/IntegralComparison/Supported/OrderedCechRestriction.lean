import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge

/-! # Ordered Cech Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechRestriction

noncomputable section

/-! A natural inclusion of open diagrams restricts the genuine supported
ordered Cech total and preserves its supported edge and global image. -/
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
  (F₁ F₂ : C ⥤ Opens X) (α : F₂ ⟶ F₁)
  {ι : Type w} [LinearOrder ι] (U : ι → C) (O : Opens X)

local instance coefficient_limits [UnivLE.{w,z}] : HasLimitsOfSize.{w,w} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{w,w,z,u}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) :=
  ModuleCat.hasColimitsOfSize.{z,u,0,0} R

def presheafTransformation :
    OrderedCechEdge.presheaves.{u,v,w,z} R X F₁ ⟶
      OrderedCechEdge.presheaves.{u,v,w,z} R X F₂ where
  app A := Functor.whiskerRight (NatTrans.op α) A.obj
  naturality A B f := by
    apply NatTrans.ext
    funext c
    exact (f.hom.naturality (α.app c.unop).op).symm

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
  (ModuleCat.{max u v w z} R)) ℕ)

def sourceMap :
    OrderedCechEdge.source.{u,v,w,z} R X F₁ O K ⟶
      OrderedCechEdge.source.{u,v,w,z} R X F₂ O K :=
  SectionsRestriction.complex O (F₁.obj (⊤_ C)) (F₂.obj (⊤_ C))
    (leOfHom (α.app (⊤_ C))) K

def presheafMap :
    OrderedCechEdge.presheafComplex.{u,v,w,z} R X F₁ K ⟶
      OrderedCechEdge.presheafComplex.{u,v,w,z} R X F₂ K :=
  (NatTrans.mapHomologicalComplex (presheafTransformation.{u,v,w,z} R X F₁ F₂ α) (.up ℕ)).app K

def bicomplexMap :
    OrderedCechEdge.bicomplex.{u,v,w,z} R X F₁ U K ⟶
      OrderedCechEdge.bicomplex.{u,v,w,z} R X F₂ U K :=
  ((AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map
    (presheafMap.{u,v,w,z} R X F₁ F₂ α K)

local instance total_exists (F : C ⥤ Opens X) :
    (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def totalMap :
    (OrderedCechEdge.bicomplex.{u,v,w,z} R X F₁ U K).total (.up ℕ) ⟶
      (OrderedCechEdge.bicomplex.{u,v,w,z} R X F₂ U K).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap.{u,v,w,z} R X F₁ F₂ α U K) (.up ℕ)

theorem component (q : ℕ) :
    (sourceMap.{u,v,w,z} R X F₁ F₂ α O K).f q ≫
        OrderedCechEdge.component.{u,v,w,z} R X F₂ U O K q =
      OrderedCechEdge.component.{u,v,w,z} R X F₁ U O K q ≫
        ((bicomplexMap.{u,v,w,z} R X F₁ F₂ α U K).f q).f 0 := by
  have h₁ := SectionsRestriction.inclusion_square O
    (F₁.obj (⊤_ C)) (F₂.obj (⊤_ C)) (leOfHom (α.app (⊤_ C))) (K.X q)
  have h₂ := AugmentedOrdered.CechZero.zeroIso_naturality U
    (F₁.op ⋙ (K.X q).obj) (Functor.whiskerRight (NatTrans.op α) (K.X q).obj)
  have hα : α.app (⊤_ C) = homOfLE (leOfHom (α.app (⊤_ C))) := Subsingleton.elim _ _
  change _ = _ ≫ (K.X q).obj.map (α.app (⊤_ C)).op at h₂
  rw [hα] at h₂
  exact inverse_square _ _ _ _ _ _ _ h₁ h₂

variable (h₁ : ∀ i, F₁.obj (U i) ≤ O) (h₂ : ∀ i, F₂.obj (U i) ≤ O)

theorem edge :
    OrderedCechEdge.map.{u,v,w,z} R X F₁ U O K h₁ ≫
        totalMap.{u,v,w,z} R X F₁ F₂ α U K =
      sourceMap.{u,v,w,z} R X F₁ F₂ α O K ≫
        OrderedCechEdge.map.{u,v,w,z} R X F₂ U O K h₂ :=
  BicomplexHorizontalEdge.naturality _ _ _ _ _ _ _ _ _ _
    (bicomplexMap.{u,v,w,z} R X F₁ F₂ α U K)
    (sourceMap.{u,v,w,z} R X F₁ F₂ α O K)
    (fun q => (component.{u,v,w,z} R X F₁ F₂ α U O K q).symm)

theorem homology (n : ℕ) :
    HomologicalComplex.homologyMap (OrderedCechEdge.map.{u,v,w,z} R X F₁ U O K h₁) n ≫
        HomologicalComplex.homologyMap (totalMap.{u,v,w,z} R X F₁ F₂ α U K) n =
      HomologicalComplex.homologyMap (sourceMap.{u,v,w,z} R X F₁ F₂ α O K) n ≫
        HomologicalComplex.homologyMap (OrderedCechEdge.map.{u,v,w,z} R X F₂ U O K h₂) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f n)
      (edge.{u,v,w,z} R X F₁ F₂ α U O K h₁ h₂)

variable
  (hc₁ : F₁.obj (⊤_ C) ⊓ O ≤ ⨆ i, F₁.obj (U i))
  (hc₂ : F₂.obj (⊤_ C) ⊓ O ≤ ⨆ i, F₂.obj (U i))
  (hr₁ : ∀ q r, ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F₁ U K).X q).ExactAt (r+1))
  (hr₂ : ∀ q r, ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F₂ U K).X q).ExactAt (r+1))
  (hg₁ : F₁.obj (⊤_ C) ⊔ O = ⊤) (hg₂ : F₂.obj (⊤_ C) ⊔ O = ⊤)

theorem forgetSupport (n : ℕ) :
    HomologicalComplex.homologyMap (totalMap.{u,v,w,z} R X F₁ F₂ α U K) n ≫
        OrderedCech.Comparison.forgetSupport.{u,v,w,z} R X F₂ U O K h₂ hc₂ hr₂ hg₂ n =
      OrderedCech.Comparison.forgetSupport.{u,v,w,z} R X F₁ U O K h₁ hc₁ hr₁ hg₁ n := by
  apply (cancel_epi (OrderedCech.Comparison.homologyIso.{u,v,w,z}
    R X F₁ U O K h₁ hc₁ hr₁ n).hom).mp
  change HomologicalComplex.homologyMap
      (OrderedCechEdge.map.{u,v,w,z} R X F₁ U O K h₁) n ≫
        (HomologicalComplex.homologyMap (totalMap.{u,v,w,z} R X F₁ F₂ α U K) n ≫ _) =
    HomologicalComplex.homologyMap
      (OrderedCechEdge.map.{u,v,w,z} R X F₁ U O K h₁) n ≫ _
  rw [← Category.assoc, homology.{u,v,w,z} R X F₁ F₂ α U O K h₁ h₂,
    Category.assoc, OrderedCech.Comparison.map_forgetSupport,
    OrderedCech.Comparison.map_forgetSupport]
  exact SectionsRestriction.homology_extension O
    (F₁.obj (⊤_ C)) (F₂.obj (⊤_ C)) (leOfHom (α.app (⊤_ C))) hg₁ hg₂ K n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechRestriction
