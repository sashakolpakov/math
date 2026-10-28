import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsLocalizedExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechCoefficientNaturality

/-! # Cech Localized Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechLocalizedExtension

noncomputable section

/-! The canonical section-supported candidate on the original supported
Cech cohomology. Restriction recovers its local class, its global image
is the genuine section extension, and coefficient fixedness is preserved. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem conjugate_section {D : Type*} [Category D]
    {A B C E : D} (e : A ≅ C) (f : B ≅ E)
    (s : B ⟶ A) (r : A ⟶ B) (t : C ⟶ E)
    (hs : s ≫ r = 𝟙 B) (ht : e.hom ≫ t = r ≫ f.hom) :
    (f.inv ≫ s ≫ e.hom) ≫ t = 𝟙 E := by
  simp only [Category.assoc]
  rw [ht, ← Category.assoc s r, hs, Category.id_comp, f.inv_hom_id]

private theorem conjugate_natural {D : Type*} [Category D]
    {A B C E A' B' C' E' : D}
    (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C') (eE : E ≅ E')
    (a : A ⟶ B) (b : C ⟶ E) (c : A ⟶ C) (d : B ⟶ E)
    (a' : A' ⟶ B') (b' : C' ⟶ E')
    (ha : eA.hom ≫ a' = a ≫ eB.hom)
    (hb : eC.hom ≫ b' = b ≫ eE.hom) (h : a ≫ d = c ≫ b) :
    a' ≫ (eB.inv ≫ d ≫ eE.hom) = (eA.inv ≫ c ≫ eC.hom) ≫ b' := by
  apply (cancel_epi eA.hom).mp
  simp only [Category.assoc]
  rw [← Category.assoc eA.hom a', ha]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hb, ← Category.assoc a d, ← Category.assoc c b, h]

universe u v w z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F₁ F₂ : C ⥤ Opens X) (α : F₂ ⟶ F₁)
  {ι : Type w} [LinearOrder ι] (U : ι → C)
  (O₁ O₂ : Opens X) (h : O₁ ≤ O₂)
  (he : F₂.obj (⊤_ C) ⊓ O₁ = F₂.obj (⊤_ C) ⊓ O₂)
  (hc : F₂.obj (⊤_ C) ⊔ O₂ = ⊤)

local instance coefficient_limits [UnivLE.{w,z}] : HasLimitsOfSize.{w,w} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{w,w,z,u}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) :=
  ModuleCat.hasColimitsOfSize.{z,u,0,0} R

def sourceTransformation :
    OrderedCechEdge.supportFunctor.{u,v,w,z} R X F₂ O₁ ⟶
      OrderedCechEdge.supportFunctor.{u,v,w,z} R X F₁ O₁ :=
  SectionsLocalizedExtension.lift O₁ O₂ (F₂.obj (⊤_ C)) h he hc ≫
    SectionsExcision.excision O₁ (F₁.obj (⊤_ C))

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
  (ModuleCat.{max u v w z} R)) ℕ)

def sourceCandidate :
    OrderedCechEdge.source.{u,v,w,z} R X F₂ O₁ K ⟶
      OrderedCechEdge.source.{u,v,w,z} R X F₁ O₁ K :=
  (NatTrans.mapHomologicalComplex (sourceTransformation.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc) (.up ℕ)).app K

def globalSectionCandidate :
    OrderedCechEdge.source.{u,v,w,z} R X F₂ O₁ K ⟶
      ((SectionsExcision.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj K :=
  SectionsLocalizedExtension.toSectionComplex O₁ O₂ (F₂.obj (⊤_ C)) he hc K ≫
    (NatTrans.mapHomologicalComplex (SectionsExcision.inclusion ⊤ O₂ le_top) (.up ℕ)).app K

theorem source_section :
    sourceCandidate.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc K ≫
      OrderedCechRestriction.sourceMap.{u,v,w,z} R X F₁ F₂ α O₁ K = 𝟙 _ := by
  have hs : sourceTransformation.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc ≫
      SectionsRestriction.map O₁ (F₁.obj (⊤_ C)) (F₂.obj (⊤_ C))
        (leOfHom (α.app (⊤_ C))) = 𝟙 _ := by
    dsimp only [sourceTransformation]
    rw [Category.assoc, SectionsRestriction.excision_square,
      SectionsLocalizedExtension.lift_restriction]
    rfl
  apply HomologicalComplex.Hom.ext
  funext n
  exact congrArg (fun a => a.app (K.X n)) hs

theorem source_global (hg : F₁.obj (⊤_ C) ⊔ O₁ = ⊤) :
    sourceCandidate.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc K ≫
        SectionsExcision.extensionComplex O₁ (F₁.obj (⊤_ C)) hg K =
      globalSectionCandidate.{u,v,w,z} R X F₂ O₁ O₂ he hc K := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((SectionsLocalizedExtension.lift O₁ O₂ (F₂.obj (⊤_ C)) h he hc).app (K.X n) ≫
      (SectionsExcision.excision O₁ (F₁.obj (⊤_ C))).app (K.X n)) ≫
        (SectionsExcision.extension O₁ (F₁.obj (⊤_ C)) hg).app (K.X n) = _
  have hx := congrArg (fun a => a.app (K.X n))
    (SectionsRestriction.excision_extension (D := ModuleCat.{max u v w z} R)
      O₁ (F₁.obj (⊤_ C)) hg)
  change (SectionsExcision.excision O₁ (F₁.obj (⊤_ C))).app (K.X n) ≫
    (SectionsExcision.extension O₁ (F₁.obj (⊤_ C)) hg).app (K.X n) = _ at hx
  rw [Category.assoc, hx]
  exact SectionsLocalizedExtension.lift_inclusion O₁ O₂ (F₂.obj (⊤_ C)) h he hc (K.X n)

theorem source_natural {L : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v w z} R)) ℕ} (a : K ⟶ L) :
    OrderedCechCoefficientNaturality.sourceMap.{u,v,w,z} R X F₂ O₁ a ≫
        sourceCandidate.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc L =
      sourceCandidate.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc K ≫
        OrderedCechCoefficientNaturality.sourceMap.{u,v,w,z} R X F₁ O₁ a :=
  (NatTrans.mapHomologicalComplex (sourceTransformation.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc) (.up ℕ)).naturality a

variable (h₁ : ∀ i, F₁.obj (U i) ≤ O₁) (h₂ : ∀ i, F₂.obj (U i) ≤ O₁)
  (hc₁ : F₁.obj (⊤_ C) ⊓ O₁ ≤ ⨆ i, F₁.obj (U i))
  (hc₂ : F₂.obj (⊤_ C) ⊓ O₁ ≤ ⨆ i, F₂.obj (U i))
  (hr₁ : ∀ q r, ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F₁ U K).X q).ExactAt (r+1))
  (hr₂ : ∀ q r, ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F₂ U K).X q).ExactAt (r+1))

local instance total_exists (F : C ⥤ Opens X)
    (M : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w z} R)) ℕ) :
    (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U M).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def candidate (n : ℕ) :=
  (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₂ U O₁ K h₂ hc₂ hr₂ n).inv ≫
    HomologicalComplex.homologyMap (sourceCandidate.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc K) n ≫
      (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₁ U O₁ K h₁ hc₁ hr₁ n).hom

theorem candidate_restriction (n : ℕ) :
    candidate.{u,v,w,z} R X F₁ F₂ U O₁ O₂ h he hc K h₁ h₂ hc₁ hc₂ hr₁ hr₂ n ≫
      HomologicalComplex.homologyMap (OrderedCechRestriction.totalMap.{u,v,w,z} R X F₁ F₂ α U K) n = 𝟙 _ := by
  apply conjugate_section
    (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₁ U O₁ K h₁ hc₁ hr₁ n)
    (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₂ U O₁ K h₂ hc₂ hr₂ n)
  · simpa only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] using
      congrArg (fun a => HomologicalComplex.homologyMap a n)
        (source_section.{u,v,w,z} R X F₁ F₂ α O₁ O₂ h he hc K)
  · exact OrderedCechRestriction.homology.{u,v,w,z} R X F₁ F₂ α U O₁ K h₁ h₂ n

theorem candidate_global (hg : F₁.obj (⊤_ C) ⊔ O₁ = ⊤) (n : ℕ) :
    candidate.{u,v,w,z} R X F₁ F₂ U O₁ O₂ h he hc K h₁ h₂ hc₁ hc₂ hr₁ hr₂ n ≫
        OrderedCech.Comparison.forgetSupport.{u,v,w,z} R X F₁ U O₁ K h₁ hc₁ hr₁ hg n =
      (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₂ U O₁ K h₂ hc₂ hr₂ n).inv ≫
        HomologicalComplex.homologyMap (globalSectionCandidate.{u,v,w,z} R X F₂ O₁ O₂ he hc K) n := by
  change ((OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₂ U O₁ K h₂ hc₂ hr₂ n).inv ≫
      HomologicalComplex.homologyMap (sourceCandidate.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc K) n ≫
        HomologicalComplex.homologyMap (OrderedCechEdge.map.{u,v,w,z} R X F₁ U O₁ K h₁) n) ≫ _ = _
  rw [Category.assoc, Category.assoc, OrderedCech.Comparison.map_forgetSupport,
    ← HomologicalComplex.homologyMap_comp, source_global]

theorem candidate_natural {L : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v w z} R)) ℕ} (a : K ⟶ L)
    (hr₁L : ∀ q r, ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F₁ U L).X q).ExactAt (r+1))
    (hr₂L : ∀ q r, ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F₂ U L).X q).ExactAt (r+1)) (n : ℕ) :
    HomologicalComplex.homologyMap (OrderedCechCoefficientNaturality.totalMap.{u,v,w,z} R X F₂ U a) n ≫
        candidate.{u,v,w,z} R X F₁ F₂ U O₁ O₂ h he hc L h₁ h₂ hc₁ hc₂ hr₁L hr₂L n =
      candidate.{u,v,w,z} R X F₁ F₂ U O₁ O₂ h he hc K h₁ h₂ hc₁ hc₂ hr₁ hr₂ n ≫
        HomologicalComplex.homologyMap (OrderedCechCoefficientNaturality.totalMap.{u,v,w,z} R X F₁ U a) n := by
  apply conjugate_natural
    (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₂ U O₁ K h₂ hc₂ hr₂ n)
    (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₂ U O₁ L h₂ hc₂ hr₂L n)
    (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₁ U O₁ K h₁ hc₁ hr₁ n)
    (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F₁ U O₁ L h₁ hc₁ hr₁L n)
  · exact OrderedCechCoefficientNaturality.homology.{u,v,w,z} R X F₂ U O₁ a h₂ n
  · exact OrderedCechCoefficientNaturality.homology.{u,v,w,z} R X F₁ U O₁ a h₁ n
  · simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun f => HomologicalComplex.homologyMap f n)
        (source_natural.{u,v,w,z} R X F₁ F₂ O₁ O₂ h he hc K a)

theorem candidate_fixed (a : K ⟶ K) (n : ℕ)
    (x : ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F₂ U K).total (.up ℕ)).homology n)
    (hx : HomologicalComplex.homologyMap
      (OrderedCechCoefficientNaturality.totalMap.{u,v,w,z} R X F₂ U a) n x = x) :
    HomologicalComplex.homologyMap
        (OrderedCechCoefficientNaturality.totalMap.{u,v,w,z} R X F₁ U a) n
        (candidate.{u,v,w,z} R X F₁ F₂ U O₁ O₂ h he hc K h₁ h₂ hc₁ hc₂ hr₁ hr₂ n x) =
      candidate.{u,v,w,z} R X F₁ F₂ U O₁ O₂ h he hc K h₁ h₂ hc₁ hc₂ hr₁ hr₂ n x := by
  have hh := ConcreteCategory.congr_hom
    (candidate_natural.{u,v,w,z} R X F₁ F₂ U O₁ O₂ h he hc K h₁ h₂ hc₁ hc₂ hr₁ hr₂ a hr₁ hr₂ n) x
  change candidate.{u,v,w,z} R X F₁ F₂ U O₁ O₂ h he hc K h₁ h₂ hc₁ hc₂ hr₁ hr₂ n
      (HomologicalComplex.homologyMap
        (OrderedCechCoefficientNaturality.totalMap.{u,v,w,z} R X F₂ U a) n x) = _ at hh
  rw [hx] at hh
  exact hh.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechLocalizedExtension
