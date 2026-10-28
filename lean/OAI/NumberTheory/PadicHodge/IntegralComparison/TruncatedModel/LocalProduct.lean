import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OpenFactor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.AmbientMono
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.BaseImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProductMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSliceMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Products

/-! # Local Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalProduct

noncomputable section

/-! Restricting a model chart to an affine intersection does not change
its crystalline product over a frame mapping into the second chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (V I : X.left.Opens) (hV : IsAffineOpen V) (hI : IsAffineOpen I)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "FV" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp V hV
local notation "FI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp I hI
local notation "FVI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp (V ⊓ I) (hV.inf hI)

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def restriction : FVI ⟶ FV :=
  FrameFunctor.map p k n X Y f hp (V ⊓ I) V (hV.inf hI) hV inf_le_left

variable (T : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k Y) n)
  (τ : T ⟶ Truncated.AffineModelFrame.frame p k n X Y f hp I hI)

include τ in
omit [X.left.IsSeparated] in
theorem base_image : Set.range (FV ⨯ T).obj.mapToX ⊆ (f ⁻¹ᵁ (V ⊓ I) : Set Y.left) := by
  have hv := GeometricComparison.Crystalline.BaseImage.CrystallineBaseImage.range_subset (prod.fst : FV ⨯ T ⟶ FV).hom
  have hi := GeometricComparison.Crystalline.BaseImage.CrystallineBaseImage.range_subset ((prod.snd : FV ⨯ T ⟶ T) ≫ τ).hom
  rw [FrameClosed.range] at hv hi
  intro y hy
  exact ⟨hv hy, hi hy⟩

def factor : FV ⨯ T ⟶ FVI :=
  ObjectProperty.homMk (OpenFactor.lift p k n X Y f hp (V ⊓ I) V
    (hV.inf hI) hV inf_le_left (FV ⨯ T).obj (prod.fst : FV ⨯ T ⟶ FV).hom
    (base_image p k n X Y f hp V I hV hI T τ))

theorem factor_comp : factor p k n X Y f hp V I hV hI T τ ≫ restriction p k n X Y f hp V I hV hI =
    (prod.fst : FV ⨯ T ⟶ FV) := by
  apply (BoundedCrystalline.Site.inclusion w n).map_injective
  exact OpenFactor.lift_comp p k n X Y f hp (V ⊓ I) V
    (hV.inf hI) hV inf_le_left (FV ⨯ T).obj (prod.fst : FV ⨯ T ⟶ FV).hom
    (base_image p k n X Y f hp V I hV hI T τ)

def iso : FVI ⨯ T ≅ FV ⨯ T := by
  letI : Mono (restriction p k n X Y f hp V I hV hI) :=
    GeometricComparison.Bounded.AmbientMono.BoundedAmbientMono.mono _ (OpenFactor.ambient_open p k n X Y f hp
      (V ⊓ I) V (hV.inf hI) hV inf_le_left)
  exact GeometricComparison.ProductMap.ProductMapOfFactorization.iso (restriction p k n X Y f hp V I hV hI)
    (factor p k n X Y f hp V I hV hI T τ) (factor_comp p k n X Y f hp V I hV hI T τ)

include τ in
theorem map_isIso : IsIso (prod.map (restriction p k n X Y f hp V I hV hI) (𝟙 T)) :=
  (iso p k n X Y f hp V I hV hI T τ).isIso_hom

theorem sliceMap_isIso : IsIso
    (((Relative.ComplexRestriction.restriction (B := WittVector p k)
      (Over.forget FI)).mapHomologicalComplex (.up ℕ)).map
        (BoundedFrame.Change.presheafMap (restriction p k n X Y f hp V I hV hI))) :=
  GeometricComparison.Frame.ChangeOnSliceMap.FrameChangeOnSliceMap.isIso w n FI FV FVI (restriction p k n X Y f hp V I hV hI)
    (fun T τ => map_isIso p k n X Y f hp V I hV hI T τ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalProduct
