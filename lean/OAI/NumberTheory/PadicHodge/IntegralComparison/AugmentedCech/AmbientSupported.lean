import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedRecovery

/-! # Ambient Supported -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientSupported

noncomputable section

/-! The ambient-open coordinate isomorphism preserves the actual
globally supported lift and hence its original global Čech class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechEdge.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable (D : Type (u+1)) [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  [HasCoproducts.{0} D]
  (X : TopCat.{u}) {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C)
  [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]
  (O : Opens X) (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)
  (hzero : ∀ q, IsZero ((K.X q).obj.obj (op O)))
  (hU : ∀ i, F.obj (U i) ≤ O)

abbrev underlying := RelativeCech.SupportedCoordinates.underlying D X K

def lift := Supported.ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hzero ≫
  SupportedOrderedCechEdge.Abelian.map D X F U O K hU

omit [HasCoproducts.{0} D] in
theorem component (q : ℕ) :
    ((Supported.ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hzero).f q ≫
      SupportedOrderedCechEdge.Abelian.component D X F U O K q) ≫
        (AmbientCoordinates.componentIso F U (K.X q).obj 0).hom =
      RelativeCech.GlobalSections.relativeAugmentation (F.obj (⊤_ C)) (F.obj ∘ U) (K.X q).obj := by
  have hlift : (Supported.ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hzero).f q ≫
      (Supported.SectionsExcision.inclusion (F.obj (⊤_ C))
        (F.obj (⊤_ C) ⊓ O) inf_le_left).app (K.X q) =
      (K.X q).obj.map (homOfLE (le_top : F.obj (⊤_ C) ≤ ⊤)).op :=
    congrArg (fun f => f.f q)
      (Supported.ZeroComplementComplex.lift_inclusion O (F.obj (⊤_ C)) K hzero)
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index ι 0)
  erw [Category.assoc, AmbientCoordinates.component_hom_π]
  erw [← Category.assoc, RelativeCech.GlobalSections.relativeAugmentation_projection]
  change (((Supported.ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hzero).f q ≫
    ((Supported.SectionsExcision.inclusion (F.obj (⊤_ C))
      (F.obj (⊤_ C) ⊓ O) inf_le_left).app (K.X q) ≫
        (AugmentedOrdered.CechZero.zeroIso U (F.op ⋙ (K.X q).obj)).inv)) ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rw [← Category.assoc ((AugmentedOrdered.CechZero.zeroIso U (F.op ⋙ (K.X q).obj)).inv),
    AugmentedOrdered.CechZero.zeroIso_inv_π]
  rw [← Category.assoc, hlift]
  change (K.X q).obj.map _ ≫ (K.X q).obj.map _ ≫ (K.X q).obj.map _ = (K.X q).obj.map _
  simp only [← Functor.map_comp]
  congr 1

theorem lift_transport : lift D X F U O K hzero hU ≫
    (AmbientTotal.totalIso F U (underlying D X K)).hom =
      RelativeCech.SupportedRecovery.localLift D X (F.obj (⊤_ C)) (F.obj ∘ U) O K hzero hU := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [lift, RelativeCech.SupportedRecovery.localLift,
    HomologicalComplex.comp_f, SupportedOrderedCechEdge.Abelian.map, AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f,
    AmbientTotal.totalIso, HomologicalComplex₂.total.mapIso_hom,
    Category.assoc, HomologicalComplex₂.ιTotal_map,
    AmbientTotal.bicomplexIso_hom_f]
  have h := (component D X F U O K hzero q).trans
    (RelativeCech.SupportedCoordinates.local_component D X (F.obj (⊤_ C))
      (F.obj ∘ U) O K hzero q).symm
  have hp : (AmbientCoordinates.componentIso F U ((underlying D X K).X q) 0).hom =
      (AmbientCoordinates.componentIso F U (K.X q).obj 0).hom := rfl
  have hb : (SupportedOrderedCechEdge.Abelian.bicomplex D X (RelativeCech.Intersections.intersect (F.obj (⊤_ C)))
      (F.obj ∘ U) K).ιTotal (.up ℕ) q 0 q rfl =
      (RelativeCech.Total.source (F.obj (⊤_ C)) (F.obj ∘ U) (underlying D X K)).ιTotal
        (.up ℕ) q 0 q rfl := rfl
  erw [hp, hb]
  simpa only [Category.assoc] using
    congrArg (fun a => a ≫
      (RelativeCech.Total.source (F.obj (⊤_ C)) (F.obj ∘ U) (underlying D X K)).ιTotal
        (.up ℕ) q 0 q rfl) h

theorem recovery : (lift D X F U O K hzero hU ≫
    (AmbientTotal.totalIso F U (underlying D X K)).hom) ≫
      RelativeCech.Total.map (F.obj (⊤_ C)) (F.obj ∘ U) (underlying D X K) =
    Presheaf.OrderedCechEdge.edge
      (RelativeCech.Intersections.cover (F.obj (⊤_ C)) (F.obj ∘ U)) (underlying D X K) := by
  rw [lift_transport]
  exact RelativeCech.SupportedRecovery.recovery D X (F.obj (⊤_ C)) (F.obj ∘ U)
    O K hzero hU

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientSupported
