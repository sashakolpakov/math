import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology
import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopZeroCycles

/-! # Pullback Global Isomorphism -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism

noncomputable section

section

/-! The actual comparison on Čech zero cycles agrees with the map on global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (G : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (α : F.obj ⟶ (Opens.map f).op ⋙ G.obj)

def additiveCechPullbackMap :
    (cechComplexFunctor U).obj F.obj ⟶
      (cechComplexFunctor (fun i => (Opens.map f).obj (U i))).obj G.obj :=
  (cechComplexFunctor U).map α ≫ (AdditiveCechImage.additiveCechDirectImageIso f U G.obj).hom

def additivePullbackGlobalSectionsMap : F.obj.obj (op ⊤) ⟶ G.obj.obj (op ⊤) :=
  α.app (op ⊤)

theorem additiveCechPullbackMap_coordinate (q : ℕ)
    (z : ((cechComplexFunctor U).obj F.obj).X q) (t : Fin (q + 1) → ι) :
    SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv G.obj (fun i => (Opens.map f).obj (U i)) q
        ((additiveCechPullbackMap f U F G α).f q z) t =
      (AdditiveCechImage.additiveCechDirectImageSectionIso f U G.obj q t).hom
        (α.app (op (∏ᶜ fun k => U (t k))) (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U q z t)) := by
  let φ := ((cechComplexFunctor U).map α).f q
  let e := (AdditiveCechImage.additiveCechDirectImageTermIso f U G.obj q).hom
  let p := CategoryTheory.Limits.Pi.π (fun a : Fin (q + 1) → ι =>
    G.obj.obj (op ((Opens.map f).obj (∏ᶜ fun k => U (a k))))) t
  let r := CategoryTheory.Limits.Pi.π (fun a : Fin (q + 1) → ι =>
    G.obj.obj (op (∏ᶜ fun k => (Opens.map f).obj (U (a k))))) t
  let p₀ := CategoryTheory.Limits.Pi.π (fun a : Fin (q + 1) → ι =>
    F.obj.obj (op (∏ᶜ fun k => U (a k)))) t
  let b := (AdditiveCechImage.additiveCechDirectImageSectionIso f U G.obj q t).hom
  have he : e ≫ r = p ≫ b := AdditiveCechImage.additiveCechDirectImageTermIso_hom_proj f U G.obj q t
  have hφ : φ ≫ p = p₀ ≫ α.app (op (∏ᶜ fun k => U (t k))) :=
    CategoryTheory.Limits.Pi.map_π (fun a : Fin (q + 1) → ι =>
      α.app (op (∏ᶜ fun k => U (a k)))) t
  have h : (φ ≫ e) ≫ r = (p₀ ≫ α.app (op (∏ᶜ fun k => U (t k)))) ≫ b :=
    (Category.assoc φ e r).trans ((congrArg (φ ≫ ·) he).trans
      ((Category.assoc φ p b).symm.trans (congrArg (· ≫ b) hφ)))
  exact (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply _ _ q _ t).trans
    ((ConcreteCategory.congr_hom h z).trans
      (congrArg (fun a => b (α.app (op (∏ᶜ fun k => U (t k))) a))
        (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply F.obj U q z t).symm))

theorem additiveCechPullbackMap_global_zeroCycle
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤)
    (x : F.obj.obj (op ⊤)) :
    AdditiveHomology.Cech.additiveZeroCycleMap (additiveCechPullbackMap f U F G α)
        (SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv U F hU x) =
      SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv (fun i => (Opens.map f).obj (U i)) G hV
        (additivePullbackGlobalSectionsMap f F G α x) := by
  apply Subtype.ext
  apply (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv G.obj (fun i => (Opens.map f).obj (U i)) 0).injective
  funext t
  change SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv G.obj (fun i => (Opens.map f).obj (U i)) 0
    ((additiveCechPullbackMap f U F G α).f 0
      (SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv U F hU x).val) t = _
  rw [additiveCechPullbackMap_coordinate, SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv_coordinate,
    SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv_coordinate]
  let a := (homOfLE (show (∏ᶜ fun k : Fin 1 => U (t k)) ≤ ⊤ from le_top)).op
  have hα := ConcreteCategory.congr_hom (α.naturality a) x
  change α.app _ (F.obj.map a x) = G.obj.map ((Opens.map f).map a.unop).op (α.app (op ⊤) x) at hα
  rw [hα]
  change G.obj.map _ (G.obj.map _ (α.app (op ⊤) x)) = G.obj.map _ (α.app (op ⊤) x)
  exact ConcreteCategory.congr_hom ((G.obj.map_comp _ _).symm.trans
    (congrArg G.obj.map (Subsingleton.elim _ _))) (α.app (op ⊤) x)

end

/-! A Čech comparison isomorphism in degree zero gives the actual global-section isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

theorem additiveZeroCycleMap_bijective_of_isIso_homologyMap
    {K L : CochainComplex AddCommGrpCat.{0} ℕ} (g : K ⟶ L) [IsIso (homologyMap g 0)] :
    Function.Bijective (AdditiveHomology.Cech.additiveZeroCycleMap g) := by
  let E := AdditiveHomology.Cech.additiveHZeroCyclesIso K
  let E' := AdditiveHomology.Cech.additiveHZeroCyclesIso L
  have h : AddCommGrpCat.ofHom (AdditiveHomology.Cech.additiveZeroCycleMap g) =
      E.inv ≫ homologyMap g 0 ≫ E'.hom :=
    (E.inv_hom_id_assoc _).symm.trans
      (congrArg (E.inv ≫ ·) (AdditiveHomology.Cech.additiveHZeroCyclesIso_naturality g))
  have : IsIso (AddCommGrpCat.ofHom (AdditiveHomology.Cech.additiveZeroCycleMap g)) := by
    rw [h]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (AddCommGrpCat.ofHom (AdditiveHomology.Cech.additiveZeroCycleMap g))

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (G : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (α : F.obj ⟶ (Opens.map f).op ⋙ G.obj)

theorem additivePullbackGlobalSectionsMap_isIso
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤)
    [IsIso (homologyMap (additiveCechPullbackMap f U F G α) 0)] :
    IsIso (additivePullbackGlobalSectionsMap f F G α) := by
  let A := SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv U F hU
  let B := SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsZeroCyclesEquiv (fun i => (Opens.map f).obj (U i)) G hV
  let ψ := AdditiveHomology.Cech.additiveZeroCycleMap (additiveCechPullbackMap f U F G α)
  let φ := additivePullbackGlobalSectionsMap f F G α
  have hψ : Function.Bijective ψ :=
    additiveZeroCycleMap_bijective_of_isIso_homologyMap (additiveCechPullbackMap f U F G α)
  have hs (x : F.obj.obj (op ⊤)) : ψ (A x) = B (φ x) :=
    additiveCechPullbackMap_global_zeroCycle f U F G α hU hV x
  apply (ConcreteCategory.isIso_iff_bijective φ).mpr
  constructor
  · intro x y h
    apply A.injective
    apply hψ.injective
    exact (hs x).trans ((congrArg B h).trans (hs y).symm)
  · intro y
    obtain ⟨z, hz⟩ := hψ.surjective (B y)
    obtain ⟨x, hx⟩ := A.surjective z
    refine ⟨x, B.injective ?_⟩
    exact (hs x).symm.trans ((congrArg ψ hx).trans hz)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism
