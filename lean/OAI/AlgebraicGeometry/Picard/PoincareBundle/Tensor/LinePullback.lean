import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackIsomorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.OpenPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleLocality

/-! # Line Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

noncomputable section

/-!
# Arbitrary geometric pullback commutes with tensor products of line bundles
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackIsomorphisms

/-- A frame on one open restricts to a frame on every smaller open. -/
def frameRestrict {Y : Scheme.{u}} (M : Y.Modules) {U V : Y.Opens} (h : U ≤ V)
    (e : (Scheme.Modules.pullback V.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V.toScheme) :
    (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme :=
  (Scheme.Modules.pullbackCongr (Y.homOfLE_ι h).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (Y.homOfLE h) V.ι).app M).symm ≪≫
      (Scheme.Modules.pullback (Y.homOfLE h)).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (Y.homOfLE h)

/-- The actual canonical tensor comparison is invertible for any morphism and any two line bundles. -/
theorem pullbackMap_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) : IsIso (PullbackMap.pullbackMap f M N) := by
  apply ModuleLocality.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM (f x)
  obtain ⟨V, hxV, ⟨eN⟩⟩ := hN (f x)
  let W := U ⊓ V
  let i := W.ι
  let j := (f ⁻¹ᵁ W).ι
  let f' := f ∣_ W
  let a := frameRestrict M (U := W) inf_le_left eM
  let b := frameRestrict N (U := W) inf_le_right eN
  have hf' : IsIso (PullbackMap.pullbackMap f' ((Scheme.Modules.pullback i).obj M) ((Scheme.Modules.pullback i).obj N)) :=
    (PullbackIsomorphisms.input_isIso_iff f' a b).mpr (UnitPullback.pullbackMap_unit_isIso f')
  have hi : IsIso (PullbackMap.pullbackMap i M N) := OpenPullback.pullbackMap_isIso i M N
  have hfi : IsIso (PullbackMap.pullbackMap (f' ≫ i) M N) := PullbackIsomorphisms.comp_isIso f' i M N hf' hi
  have hjf : IsIso (PullbackMap.pullbackMap (j ≫ f) M N) := by
    rw [← morphismRestrict_ι f W]
    exact hfi
  have hj : IsIso (PullbackMap.pullbackMap j ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)) :=
    OpenPullback.pullbackMap_isIso j _ _
  have hm : IsIso ((Scheme.Modules.pullback j).map (PullbackMap.pullbackMap f M N)) :=
    (PullbackIsomorphisms.comp_map_isIso_iff j f M N hj).mp hjf
  exact ⟨f ⁻¹ᵁ W, ⟨hxU, hxV⟩,
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback j) (PullbackMap.pullbackMap f M N)).mpr hm⟩

/-- The canonical tensor pullback isomorphism for actual line-bundle sheaves. -/
def pullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  @asIso _ _ _ _ (PullbackMap.pullbackMap f M N) (pullbackMap_isIso f M N hM hN)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback
