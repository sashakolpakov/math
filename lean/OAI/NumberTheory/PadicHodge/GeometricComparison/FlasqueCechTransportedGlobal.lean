import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TransportedCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechTopConeCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainEdge

/-! # Flasque Cech Transported Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison

noncomputable section

/-! A flasque global comparison retains arbitrary original section
coordinate isomorphisms throughout its Cech and homology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v w s t
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R)) ℕ)
  {C : Type s} [Category.{t} C] [HasBinaryProducts C] (F : C ⥤ Opens X)
  {ι : Type} (U : ι → C)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  {Q : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{max u v w} R) ℕ}
  {N : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v w} R) ℕ}
  (e₀ : N ≅ ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{max u v w} R) F).mapHomologicalComplex (.up ℕ)).obj Q)
  (e₁ : FlasqueCechGlobal.FlasqueCechGlobalComparison.presheafComplex R X K ≅ Q)

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.presheafComplex R X K
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.globalComplex R X K

def cone := Cech.TransportedCone.CechTransportedCone.cone F e₀ e₁ M (CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) P)
def edge := Cech.TransportedCone.CechTransportedCone.edge F U e₀ e₁ M (CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) P)
def comparisonIso := HomologicalComplex₂.total.mapIso (Cech.TransportedCone.CechTransportedCone.bicomplexIso F U e₀ e₁) (.up ℕ)

theorem comparison : edge R X K F U e₀ e₁ ≫ (comparisonIso R X K F U e₀ e₁).hom =
    FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X (F.obj ∘ U) K :=
  (Cech.TransportedCone.CechTransportedCone.edge_comparison F U e₀ e₁ M (CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) P)).trans
    (CechTopConeCoordinates.FlasqueCechTopConeCoordinates.map_eq R X (F.obj ∘ U) K)

variable (hU : iSup (F.obj ∘ U) = ⊤)
  (hK : ∀ q, TopCat.Presheaf.IsFlasque (X := X) (K.X q).obj)

include hU hK in
theorem quasiIso : QuasiIso (edge R X K F U e₀ e₁) := by
  have h : QuasiIso (edge R X K F U e₀ e₁ ≫ (comparisonIso R X K F U e₀ e₁).hom) :=
    (comparison R X K F U e₀ e₁).symm ▸ FlasqueCechGlobal.FlasqueCechGlobalComparison.quasiIso R X (F.obj ∘ U) K hU hK
  exact (quasiIso_iff_comp_right _ (comparisonIso R X K F U e₀ e₁).hom).mp h

def homologyIso (i : ℕ) {B : ModuleCat.{max u v w} R} (k : (M).homology i ≅ B) :
    ((CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U N).total (.up ℕ)).homology i ≅ B := by
  letI : QuasiIso (FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X (F.obj ∘ U) K) :=
    FlasqueCechGlobal.FlasqueCechGlobalComparison.quasiIso R X (F.obj ∘ U) K hU hK
  exact (HomologicalComplex.homologyFunctor _ _ i).mapIso (comparisonIso R X K F U e₀ e₁) ≪≫
    (asIso (HomologicalComplex.homologyMap (FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X (F.obj ∘ U) K) i)).symm ≪≫ k

theorem homology (i : ℕ) {B : ModuleCat.{max u v w} R} (k : (M).homology i ≅ B) :
    HomologicalComplex.homologyMap (edge R X K F U e₀ e₁) i ≫
      (homologyIso R X K F U e₀ e₁ hU hK i k).hom = k.hom := by
  exact @CochainEdge.CochainEdgeComparison.homology (ModuleCat.{max u v w} R) _ _ _ _ _
    (edge R X K F U e₀ e₁) (comparisonIso R X K F U e₀ e₁)
    (FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X (F.obj ∘ U) K) (comparison R X K F U e₀ e₁)
    (FlasqueCechGlobal.FlasqueCechGlobalComparison.quasiIso R X (F.obj ∘ U) K hU hK) i _ k

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison
