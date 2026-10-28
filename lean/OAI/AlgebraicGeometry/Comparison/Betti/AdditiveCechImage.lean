import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr
import Mathlib.Topology.Sheaves.Functors

/-! # Additive Cech Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

noncomputable section

section

/-! Actual additive Čech intersection sections commute with a continuous inverse image of opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped Simplicial

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)

theorem additiveCechIntersection_preimage (q : ℕ) (t : Fin (q + 1) → ι) :
    (Opens.map f).obj (∏ᶜ fun k : Fin (q + 1) => U (t k)) =
      ∏ᶜ fun k : Fin (q + 1) => (Opens.map f).obj (U (t k)) := by
  rw [SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf, SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf]
  ext y
  change (f y ∈ ⨅ k : Fin (q + 1), U (t k)) ↔
    y ∈ ⨅ k : Fin (q + 1), (Opens.map f).obj (U (t k))
  simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl

variable (F : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0})

def additiveCechDirectImageSectionIso (q : ℕ) (t : Fin (q + 1) → ι) :
    F.obj (op ((Opens.map f).obj (∏ᶜ fun k : Fin (q + 1) => U (t k)))) ≅
      F.obj (op (∏ᶜ fun k : Fin (q + 1) => (Opens.map f).obj (U (t k)))) :=
  F.mapIso (eqToIso (congrArg op (additiveCechIntersection_preimage f U q t)))

theorem additiveCechDirectImageSectionIso_precomp {a b : SimplexCategory} (g : a ⟶ b)
    (t : Fin (b.len + 1) → ι) :
    F.map ((Opens.map f).map (((FormalCoproduct.mk _ U).mapPower g.toOrderHom).φ t)).op ≫
        (additiveCechDirectImageSectionIso f U F b.len t).hom =
      (additiveCechDirectImageSectionIso f U F a.len (t ∘ g.toOrderHom)).hom ≫
        F.map (((FormalCoproduct.mk _ (fun i => (Opens.map f).obj (U i))).mapPower
          g.toOrderHom).φ t).op := by
  change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (Subsingleton.elim _ _)).trans (F.map_comp _ _))

end

section

/-! The original additive Čech complex of a direct image is the complex on the inverse-image cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped Simplicial

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)
    (F : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0})

def additiveCechDirectImageTermIso (q : ℕ) :
    ((cechComplexFunctor U).obj ((Opens.map f).op ⋙ F)).X q ≅
      ((cechComplexFunctor (fun i => (Opens.map f).obj (U i))).obj F).X q :=
  Pi.mapIso (fun t : Fin (q + 1) → ι => additiveCechDirectImageSectionIso f U F q t)

@[reassoc]
theorem additiveCechDirectImageTermIso_hom_proj (q : ℕ) (t : Fin (q + 1) → ι) :
    (additiveCechDirectImageTermIso f U F q).hom ≫
        Pi.π (fun a : Fin (q + 1) → ι =>
          F.obj (op (∏ᶜ fun k => (Opens.map f).obj (U (a k))))) t =
      Pi.π (fun a : Fin (q + 1) → ι =>
          F.obj (op ((Opens.map f).obj (∏ᶜ fun k => U (a k))))) t ≫
        (additiveCechDirectImageSectionIso f U F q t).hom :=
  Pi.mapIso_hom_π _ _

theorem additiveCechDirectImageTermIso_naturality {a b : SimplexCategory} (g : a ⟶ b) :
    (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        ((Opens.map f).op ⋙ F)).map g) ≫ (additiveCechDirectImageTermIso f U F b.len).hom =
      (additiveCechDirectImageTermIso f U F a.len).hom ≫
        (((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ (fun i => (Opens.map f).obj (U i))).cech).obj F).map g) := by
  apply Pi.hom_ext
  intro t
  let S := (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
    ((Opens.map f).op ⋙ F)
  let T := (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ (fun i => (Opens.map f).obj (U i))).cech).obj F
  let e₀ := (additiveCechDirectImageTermIso f U F a.len).hom
  let e₁ := (additiveCechDirectImageTermIso f U F b.len).hom
  let p₀ := Pi.π (fun u : Fin (a.len + 1) → ι =>
    F.obj (op ((Opens.map f).obj (∏ᶜ fun k => U (u k))))) (t ∘ g.toOrderHom)
  let p₁ := Pi.π (fun u : Fin (b.len + 1) → ι =>
    F.obj (op ((Opens.map f).obj (∏ᶜ fun k => U (u k))))) t
  let r₀ := Pi.π (fun u : Fin (a.len + 1) → ι =>
    F.obj (op (∏ᶜ fun k => (Opens.map f).obj (U (u k))))) (t ∘ g.toOrderHom)
  let r₁ := Pi.π (fun u : Fin (b.len + 1) → ι =>
    F.obj (op (∏ᶜ fun k => (Opens.map f).obj (U (u k))))) t
  let b₀ := (additiveCechDirectImageSectionIso f U F a.len (t ∘ g.toOrderHom)).hom
  let b₁ := (additiveCechDirectImageSectionIso f U F b.len t).hom
  let s := F.map ((Opens.map f).map (((FormalCoproduct.mk _ U).mapPower g.toOrderHom).φ t)).op
  let r := F.map (((FormalCoproduct.mk _ (fun i => (Opens.map f).obj (U i))).mapPower
    g.toOrderHom).φ t).op
  have h₁ : e₁ ≫ r₁ = p₁ ≫ b₁ := additiveCechDirectImageTermIso_hom_proj f U F b.len t
  have h₀ : e₀ ≫ r₀ = p₀ ≫ b₀ :=
    additiveCechDirectImageTermIso_hom_proj f U F a.len (t ∘ g.toOrderHom)
  have hs : S.map g ≫ p₁ = p₀ ≫ s := AdditiveCechCoverCongr.additiveCechMap_proj ((Opens.map f).op ⋙ F) U g t
  have hr : T.map g ≫ r₁ = r₀ ≫ r :=
    AdditiveCechCoverCongr.additiveCechMap_proj F (fun i => (Opens.map f).obj (U i)) g t
  have hl : (S.map g ≫ e₁) ≫ r₁ = p₀ ≫ (s ≫ b₁) :=
    (Category.assoc _ _ _).trans ((congrArg (S.map g ≫ ·) h₁).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b₁) hs).trans (Category.assoc _ _ _))))
  have hr' : (e₀ ≫ T.map g) ≫ r₁ = p₀ ≫ (b₀ ≫ r) :=
    (Category.assoc _ _ _).trans ((congrArg (e₀ ≫ ·) hr).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r) h₀).trans (Category.assoc _ _ _))))
  exact hl.trans ((congrArg (p₀ ≫ ·)
    (additiveCechDirectImageSectionIso_precomp f U F g t)).trans hr'.symm)

def additiveCechDirectImageCosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj ((Opens.map f).op ⋙ F) ≅
      (FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ (fun i => (Opens.map f).obj (U i))).cech).obj F :=
  NatIso.ofComponents (fun q => additiveCechDirectImageTermIso f U F q.len)
    (fun g => additiveCechDirectImageTermIso_naturality f U F g)

def additiveCechDirectImageIso :
    (cechComplexFunctor U).obj ((Opens.map f).op ⋙ F) ≅
      (cechComplexFunctor (fun i => (Opens.map f).obj (U i))).obj F :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).mapIso
    (additiveCechDirectImageCosimplicialIso f U F)

theorem additiveCechDirectImageIso_hom_f (q : ℕ) :
    (additiveCechDirectImageIso f U F).hom.f q = (additiveCechDirectImageTermIso f U F q).hom := rfl

end

section

/-! The native Čech direct-image identification is natural in the additive coefficient presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)
    {F G : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} (α : F ⟶ G)

theorem additiveCechDirectImageSectionIso_naturality (q : ℕ) (t : Fin (q + 1) → ι) :
    α.app (op ((Opens.map f).obj (∏ᶜ fun k => U (t k)))) ≫
        (additiveCechDirectImageSectionIso f U G q t).hom =
      (additiveCechDirectImageSectionIso f U F q t).hom ≫
        α.app (op (∏ᶜ fun k => (Opens.map f).obj (U (t k)))) :=
  (α.naturality (eqToHom (congrArg op (additiveCechIntersection_preimage f U q t)))).symm

theorem additiveCechDirectImageIso_naturality :
    (cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map f).op α) ≫
        (additiveCechDirectImageIso f U G).hom =
      (additiveCechDirectImageIso f U F).hom ≫
        (cechComplexFunctor (fun i => (Opens.map f).obj (U i))).map α := by
  apply HomologicalComplex.Hom.ext
  funext q
  change CategoryTheory.Limits.Pi.map (fun t : Fin (q + 1) → ι =>
      α.app (op ((Opens.map f).obj (∏ᶜ fun k => U (t k))))) ≫
      CategoryTheory.Limits.Pi.map (fun t : Fin (q + 1) → ι => (additiveCechDirectImageSectionIso f U G q t).hom) =
    CategoryTheory.Limits.Pi.map (fun t : Fin (q + 1) → ι => (additiveCechDirectImageSectionIso f U F q t).hom) ≫
      CategoryTheory.Limits.Pi.map (fun t : Fin (q + 1) → ι => α.app (op (∏ᶜ fun k => (Opens.map f).obj (U (t k)))))
  rw [CategoryTheory.Limits.Pi.map_comp_map, CategoryTheory.Limits.Pi.map_comp_map]
  apply congrArg CategoryTheory.Limits.Pi.map
  funext t
  exact additiveCechDirectImageSectionIso_naturality f U α q t

end

section

/-! The canonical additive Čech direct-image isomorphisms compose along actual continuous maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

theorem additiveCechDirectImageIso_comp
    {X Y Z : TopCat.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) {ι : Type} (U : ι → Opens X)
    (F : (Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{0}) :
    (additiveCechDirectImageIso (g ≫ f) U F).hom =
      (additiveCechDirectImageIso f U ((Opens.map g).op ⋙ F)).hom ≫
        (additiveCechDirectImageIso g (fun i => (Opens.map f).obj (U i)) F).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  change CategoryTheory.Limits.Pi.map
      (fun t : Fin (q + 1) → ι => (additiveCechDirectImageSectionIso (g ≫ f) U F q t).hom) =
    CategoryTheory.Limits.Pi.map
      (fun t : Fin (q + 1) → ι => (additiveCechDirectImageSectionIso f U
        ((Opens.map g).op ⋙ F) q t).hom) ≫
    CategoryTheory.Limits.Pi.map
      (fun t : Fin (q + 1) → ι => (additiveCechDirectImageSectionIso g
        (fun i => (Opens.map f).obj (U i)) F q t).hom)
  rw [CategoryTheory.Limits.Pi.map_comp_map]
  apply congrArg CategoryTheory.Limits.Pi.map
  funext t
  change F.map _ = F.map _ ≫ F.map _
  exact (congrArg F.map (Subsingleton.elim _ _)).trans (F.map_comp _ _)

end

/-! Two naturality formulas for the original additive Čech pullback maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem additiveCechPullback_postcompose
    {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)
    {F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {G H : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (α : F ⟶ (Opens.map f).op ⋙ G) (β : G ⟶ H) :
    ((cechComplexFunctor U).map α ≫ (additiveCechDirectImageIso f U G).hom) ≫
        (cechComplexFunctor (fun i => (Opens.map f).obj (U i))).map β =
      (cechComplexFunctor U).map (α ≫ Functor.whiskerLeft (Opens.map f).op β) ≫
        (additiveCechDirectImageIso f U H).hom := by
  rw [(cechComplexFunctor U).map_comp, Category.assoc, Category.assoc,
    additiveCechDirectImageIso_naturality]

theorem additiveCechPullback_directImage
    {X Y Z : TopCat.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) {ι : Type} (U : ι → Opens X)
    {F : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} {G : (Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (α : F ⟶ (Opens.map g).op ⋙ G) :
    (cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map f).op α) ≫
        (additiveCechDirectImageIso (g ≫ f) U G).hom =
      (additiveCechDirectImageIso f U F).hom ≫
        ((cechComplexFunctor (fun i => (Opens.map f).obj (U i))).map α ≫
          (additiveCechDirectImageIso g (fun i => (Opens.map f).obj (U i)) G).hom) := by
  let c := (cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map f).op α)
  let e := (additiveCechDirectImageIso g (fun i => (Opens.map f).obj (U i)) G).hom
  exact (congrArg (c ≫ ·) (additiveCechDirectImageIso_comp f g U G)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ e) (additiveCechDirectImageIso_naturality f U α)).trans
        (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage
