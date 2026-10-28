import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechAmbientExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover

/-! # Supported Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedCover.Comparison

noncomputable section

/-! The original principal-to-cover comparison on a resolution is
its canonical support-forgetting map followed by the global Čech edge.
All ambient coordinates and both common refinements are retained. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z
variable (R : Type u) [CommRing R] (X : TopCat.{v})

local instance coefficient_limits [UnivLE.{v,z}] : HasLimitsOfSize.{v,v} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{v,v,z,u}
local instance coefficient_products [UnivLE.{v,z}] : HasProducts.{v} (ModuleCat.{z} R) :=
  fun J => by
    let : HasLimitsOfSize.{v,v} (ModuleCat.{z} R) := ModuleCat.hasLimitsOfSize.{v,v,z,u}
    exact HasLimitsOfSize.has_limits_of_shape (Discrete J)
local instance coefficient_coproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun J => by
    let : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) := ModuleCat.hasColimitsOfSize.{z,u,0,0} R
    exact HasColimitsOfSize.has_colimits_of_shape (Discrete J)

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v z} R)) ℕ)

section Refinement
variable (A : Opens X) {ι κ : Type v} [LinearOrder ι] [LinearOrder κ]
  (V : ι → Opens X) (W : κ → Opens X)
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V) (O : Opens X)

private theorem relative_component (q : ℕ) :
    Supported.OrderedCechEdge.component.{u,v,v,z} R X (RelativeCech.Intersections.intersect A) V O K q ≫
      ((AugmentedOrdered.CechRefinementTotal.bicomplexMap V W r
        (Supported.OrderedCechEdge.presheafComplex.{u,v,v,z} R X (RelativeCech.Intersections.intersect A) K)).f q).f 0 =
    Supported.OrderedCechEdge.component.{u,v,v,z} R X (RelativeCech.Intersections.intersect A) W O K q := by
  change (_ ≫ (AugmentedOrdered.CechZero.zeroIso V ((RelativeCech.Intersections.intersect A).op ⋙ (K.X q).obj)).inv) ≫
      (AugmentedOrdered.CechRefinement.map V W r ((RelativeCech.Intersections.intersect A).op ⋙ (K.X q).obj)).f 0 = _
  rw [AugmentedOrdered.CechRefinement.map_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private theorem relative_edge (hV : ∀ i, V i ≤ O) (hW : ∀ i, W i ≤ O) :
    Supported.OrderedCechEdge.map.{u,v,v,z} R X (RelativeCech.Intersections.intersect A) V O K
        (fun i => inf_le_right.trans (hV i)) ≫
      RelativeCech.Refinement.map A V W r
        (Relative.SupportedExtension.underlying.{u,v,z} R X K) =
    Supported.OrderedCechEdge.map.{u,v,v,z} R X (RelativeCech.Intersections.intersect A) W O K
      (fun i => inf_le_right.trans (hW i)) := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [Supported.OrderedCechEdge.map, HomologicalComplex.comp_f,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f,
    RelativeCech.Refinement.map, AugmentedOrdered.CechRefinementTotal.totalMap,
    Category.assoc, HomologicalComplex₂.ιTotal_map]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫
      (Supported.OrderedCechEdge.bicomplex.{u,v,v,z} R X (RelativeCech.Intersections.intersect A) W K).ιTotal
        (.up ℕ) q 0 q rfl) (relative_component R X K A V W r O q))
end Refinement

variable {C : Type v} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type v}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (O : Opens X) (hW : ∀ i, F.obj (W i) ≤ O) (hB : ∀ i, B i ≤ O)
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (Relative.SupportedExtension.underlying.{u,v,z} R X K) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (Relative.SupportedExtension.underlying.{u,v,z} R X K)) q)]

include hB in
theorem edge_comparison :
    homologyMap (Supported.OrderedCechEdge.map.{u,v,v,z} R X F W O K hW) q ≫
      PresheafCover.Comparison.comparison F W B J r s V T l t
        (Relative.SupportedExtension.underlying.{u,v,z} R X K) q =
    homologyMap (Supported.SectionsExcision.extensionComplex O (F.obj (⊤_ C)) hglobal K) q ≫
      homologyMap (Presheaf.OrderedCechEdge.edge V
        (Relative.SupportedExtension.underlying.{u,v,z} R X K)) q := by
  let P := Relative.SupportedExtension.underlying.{u,v,z} R X K
  let A := F.obj (⊤_ C)
  let hA := Supported.CechAmbientExtension.relative_global X F O hglobal
  let hJ : ∀ j, J j ≤ O := fun j => (leOfHom (r.φ j)).trans (hW (r.f j))
  let eF := homologyMap (Supported.OrderedCechEdge.map.{u,v,v,z} R X F W O K hW) q
  let a := homologyMap (AugmentedCech.AmbientTotal.totalIso F W P).hom q
  let eI := homologyMap (Supported.CechAmbientExtension.sourceIso R X F O K).hom q
  let eW := homologyMap (Supported.OrderedCechEdge.map.{u,v,v,z} R X (RelativeCech.Intersections.intersect A)
    (F.obj ∘ W) O K (fun i => inf_le_right.trans (hW i))) q
  let eB := homologyMap (Supported.OrderedCechEdge.map.{u,v,v,z} R X (RelativeCech.Intersections.intersect A)
    B O K (fun i => inf_le_right.trans (hB i))) q
  let eJ := homologyMap (Supported.OrderedCechEdge.map.{u,v,v,z} R X (RelativeCech.Intersections.intersect A)
    J O K (fun i => inf_le_right.trans (hJ i))) q
  let rmap := RelativeCech.Refinement.homology A (F.obj ∘ W) J r P q
  let smap := RelativeCech.Refinement.homology A B J s P q
  let d := homologyMap (RelativeCech.Total.map A B P) q
  let gmap := Presheaf.OrderedCover.Comparison.comparison (RelativeCech.Intersections.cover A B) V T l t P q
  let eExt := homologyMap (Supported.SectionsExcision.extensionComplex O
    ((RelativeCech.Intersections.intersect A).obj (⊤_ (Opens X))) hA K) q
  let eOut := homologyMap (Supported.SectionsExcision.extensionComplex O A hglobal K) q
  let eCover := homologyMap (Presheaf.OrderedCechEdge.edge (RelativeCech.Intersections.cover A B) P) q
  let eTarget := homologyMap (Presheaf.OrderedCechEdge.edge V P) q
  have ha := congrArg (fun a => homologyMap a q)
    (Supported.CechAmbientExtension.ambient_edge R X F W O K hglobal hW)
  simp only [homologyMap_comp] at ha
  change eF ≫ a = eI ≫ eW at ha
  have hr := congrArg (fun a => homologyMap a q)
    (relative_edge R X K A (F.obj ∘ W) J r O hW hJ)
  simp only [homologyMap_comp] at hr
  change eW ≫ rmap = eJ at hr
  have hs := congrArg (fun a => homologyMap a q)
    (relative_edge R X K A B J s O hB hJ)
  simp only [homologyMap_comp] at hs
  change eB ≫ smap = eJ at hs
  have he := congrArg (fun a => homologyMap a q)
    (Relative.SupportedExtension.comparison R X A B O K hA hB)
  simp only [Relative.SupportedExtension.relativeMap,
    Relative.SupportedExtension.globalMap, homologyMap_comp] at he
  change eB ≫ d = eExt ≫ eCover at he
  have hI := congrArg (fun a => homologyMap a q)
    (Supported.CechAmbientExtension.extension R X F O K hglobal)
  simp only [homologyMap_comp] at hI
  change eI ≫ eExt = eOut at hI
  have hg : eCover ≫ gmap = eTarget :=
    Presheaf.OrderedCover.Comparison.edge (RelativeCech.Intersections.cover A B) V T l t P q
  dsimp only [PresheafCover.Comparison.comparison,
    Relative.PresheafCommonRefinement.comparison]
  simp only [homologyMapIso_hom, Category.assoc]
  change eF ≫ a ≫ rmap ≫ inv smap ≫ d ≫ gmap = eOut ≫ eTarget
  calc
    _ = eI ≫ eW ≫ rmap ≫ inv smap ≫ d ≫ gmap := by
      rw [← Category.assoc eF a, ha, Category.assoc]
    _ = eI ≫ eJ ≫ inv smap ≫ d ≫ gmap := by
      rw [← Category.assoc eW rmap, hr]
    _ = eI ≫ eB ≫ d ≫ gmap := by
      rw [← hs]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = eI ≫ eExt ≫ eCover ≫ gmap := by
      rw [← Category.assoc eB d, he]
      simp only [Category.assoc]
    _ = _ := by rw [← Category.assoc eI eExt, hI, hg]

variable (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (W i))
  (hrows : ∀ n m, ((Supported.OrderedCechEdge.bicomplex.{u,v,v,z} R X F W K).X n).ExactAt (m+1))

include hB in
theorem comparison :
    PresheafCover.Comparison.comparison F W B J r s V T l t
      (Relative.SupportedExtension.underlying.{u,v,z} R X K) q =
    Supported.OrderedCech.Comparison.forgetSupport.{u,v,v,z}
      R X F W O K hW hcover hrows hglobal q ≫
      homologyMap (Presheaf.OrderedCechEdge.edge V
        (Relative.SupportedExtension.underlying.{u,v,z} R X K)) q := by
  let := Supported.OrderedCech.Comparison.quasiIso.{u,v,v,z}
    R X F W O K hW hcover hrows
  apply (cancel_epi (homologyMap
    (Supported.OrderedCechEdge.map.{u,v,v,z} R X F W O K hW) q)).mp
  exact (edge_comparison R X K F W B J r s V T l t O hW hB hglobal q).trans
    (((congrArg (fun a => a ≫ homologyMap (Presheaf.OrderedCechEdge.edge V
      (Relative.SupportedExtension.underlying.{u,v,z} R X K)) q)
      (Supported.OrderedCech.Comparison.map_forgetSupport.{u,v,v,z}
        R X F W O K hW hcover hrows hglobal q)).symm).trans (Category.assoc _ _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedCover.Comparison
