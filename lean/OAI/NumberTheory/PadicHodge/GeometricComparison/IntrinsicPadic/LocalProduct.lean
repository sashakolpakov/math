import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenFactor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.AmbientMono
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.BaseImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProductMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Products

/-! # Local Product -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalProduct.IntrinsicPadicLocalProduct

noncomputable section

/-! Over an object mapping into a native affine frame, intersecting another
chart with that open leaves its actual crystalline product unchanged. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (V I : X.left.Opens) (hV : IsAffineOpen V) (hI : IsAffineOpen I)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "FV" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp V hV n
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I hI n
local notation "FVI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (V ⊓ I) (hV.inf hI) n

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def restriction : FVI ⟶ FV :=
  PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp (V ⊓ I) V (hV.inf hI) hV inf_le_left n

variable (T : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n)
  (τ : T ⟶ ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I hI n)

include τ in
omit [X.left.IsSeparated] in
theorem base_image : Set.range (FV ⨯ T).obj.mapToX ⊆ (f ⁻¹ᵁ (V ⊓ I) : Set Y.left) := by
  have hv := Crystalline.BaseImage.CrystallineBaseImage.range_subset (prod.fst : FV ⨯ T ⟶ FV).hom
  have hi := Crystalline.BaseImage.CrystallineBaseImage.range_subset ((prod.snd : FV ⨯ T ⟶ T) ≫ τ).hom
  rw [FrameClosed.IntrinsicPadicFrameClosed.range] at hv hi
  intro y hy
  exact ⟨hv hy, hi hy⟩

def factor : FV ⨯ T ⟶ FVI :=
  ObjectProperty.homMk (OpenFactor.IntrinsicPadicOpenFactor.lift p X Y f hp n (V ⊓ I) V
    (hV.inf hI) hV inf_le_left (FV ⨯ T).obj (prod.fst : FV ⨯ T ⟶ FV).hom
    (base_image p X Y f hp n V I hV hI T τ))

theorem factor_comp : factor p X Y f hp n V I hV hI T τ ≫ restriction p X Y f hp n V I hV hI =
    (prod.fst : FV ⨯ T ⟶ FV) := by
  apply (IntegralComparison.BoundedCrystalline.Site.inclusion w n).map_injective
  exact OpenFactor.IntrinsicPadicOpenFactor.lift_comp p X Y f hp n (V ⊓ I) V
    (hV.inf hI) hV inf_le_left (FV ⨯ T).obj (prod.fst : FV ⨯ T ⟶ FV).hom
    (base_image p X Y f hp n V I hV hI T τ)

def iso : FVI ⨯ T ≅ FV ⨯ T := by
  letI : Mono (restriction p X Y f hp n V I hV hI) :=
    Bounded.AmbientMono.BoundedAmbientMono.mono _ (OpenFactor.IntrinsicPadicOpenFactor.ambient_open p X Y f hp n
      (V ⊓ I) V (hV.inf hI) hV inf_le_left)
  exact ProductMap.ProductMapOfFactorization.iso (restriction p X Y f hp n V I hV hI)
    (factor p X Y f hp n V I hV hI T τ) (factor_comp p X Y f hp n V I hV hI T τ)

include τ in
theorem map_isIso : IsIso (prod.map (restriction p X Y f hp n V I hV hI) (𝟙 T)) :=
  (iso p X Y f hp n V I hV hI T τ).isIso_hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalProduct.IntrinsicPadicLocalProduct
