import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechTopConeCoordinates

/-! # Flasque Cech Indexed Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison

noncomputable section

/-! A cover indexed through a product-preserving functor computes
the original global sections of a flasque complex by its canonical edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v w s t
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R)) ℕ)
  {C : Type s} [Category.{t} C] [HasBinaryProducts C] (F : C ⥤ Opens X)
  {ι : Type} (U : ι → C)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.presheafComplex R X K
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.globalComplex R X K

def sections : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v w} R) ℕ :=
  ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{max u v w} R) F).mapHomologicalComplex (.up ℕ)).obj P

def cone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ sections R X K F :=
  CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F P M (CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) P)

def bicomplex := CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (sections R X K F)

def map : M ⟶ (bicomplex R X K F U).total (.up ℕ) :=
  CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (sections R X K F) M (cone R X K F)

def productIso : (bicomplex R X K F U).total (.up ℕ) ≅
    (FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex R X (F.obj ∘ U) K).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U P) (.up ℕ)

theorem map_product : map R X K F U ≫ (productIso R X K F U).hom =
    FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X (F.obj ∘ U) K :=
  (CechPresheaf.ConeProduct.CechPresheafConeProduct.augmentation F U P M (CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) P)).trans
    (CechTopConeCoordinates.FlasqueCechTopConeCoordinates.map_eq R X (F.obj ∘ U) K)

variable (hU : iSup (F.obj ∘ U) = ⊤)
  (hK : ∀ q, TopCat.Presheaf.IsFlasque (X := X) (K.X q).obj)

include hU hK in
theorem quasiIso : QuasiIso (map R X K F U) := by
  have h : QuasiIso (map R X K F U ≫ (productIso R X K F U).hom) :=
    (map_product R X K F U).symm ▸ FlasqueCechGlobal.FlasqueCechGlobalComparison.quasiIso R X (F.obj ∘ U) K hU hK
  exact (quasiIso_iff_comp_right (map R X K F U) (productIso R X K F U).hom).mp h

def homologyIso (i : ℕ) : ((bicomplex R X K F U).total (.up ℕ)).homology i ≅ (M).homology i := by
  letI : QuasiIso (map R X K F U) := quasiIso R X K F U hU hK
  exact (asIso (HomologicalComplex.homologyMap (map R X K F U) i)).symm

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (map R X K F U) i ≫
    (homologyIso R X K F U hU hK i).hom = 𝟙 ((M).homology i) := by
  let : QuasiIso (map R X K F U) := quasiIso R X K F U hU hK
  exact (asIso (HomologicalComplex.homologyMap (map R X K F U) i)).hom_inv_id

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechIndexedGlobal.FlasqueCechIndexedGlobalComparison
