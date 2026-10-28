import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModuleMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesDeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

/-! # Coordinates Module Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModuleComplex

noncomputable section

/-!
# IntegralComparison: the relative resolution with the original crystalline coefficients

The relative differential is linear over each original ambient ring,
hence over the original base. The canonical augmentation starts at the
same module presheaf used to define the original crystalline cohomology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesForms

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (σ : Type u)

def differential (n : ℕ) :
    CoordinatesModuleMaps.formsPresheaf (p := p) (B := B) (J := J) (δ := δ) (f := f) σ n ⟶
      CoordinatesModuleMaps.formsPresheaf σ (n + 1) where
  app U := (ModuleCat.restrictScalars U.unop.base).map
    (ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential U.unop.ring (Crystalline.DividedCoordinates.object U.unop σ).ring
      (Crystalline.DividedCoordinates.object U.unop σ).ideal (Crystalline.DividedCoordinates.object U.unop σ).dividedPowers n))
  naturality _ _ α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact (CoordinatesForms.formsMap_differential σ α.unop n ω).symm

theorem differential_square (n : ℕ) :
    differential (p := p) (B := B) (J := J) (δ := δ) (f := f) σ n ≫ differential σ (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_square U.unop.ring (Crystalline.DividedCoordinates.object U.unop σ).ring
    (Crystalline.DividedCoordinates.object U.unop σ).ideal (Crystalline.DividedCoordinates.object U.unop σ).dividedPowers n ω

def complex : CochainComplex ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B) ℕ :=
  CochainComplex.of (CoordinatesModuleMaps.formsPresheaf σ) (differential σ) (differential_square σ)

theorem complex_d (n : ℕ) :
    (complex (p := p) (B := B) (J := J) (δ := δ) (f := f) σ).d n (n + 1) = differential σ n :=
  CochainComplex.of_d _ _ n

def constantsLinear (U : BigCrystallineSite.Object p B J δ f) : U.ring →ₗ[U.ring] CoordinatesForms.Forms σ U 0 :=
  ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv U.ring (Crystalline.DividedCoordinates.object U σ).ring (Crystalline.DividedCoordinates.object U σ).ideal
    (Crystalline.DividedCoordinates.object U σ).dividedPowers).symm.restrictScalars U.ring).toLinearMap.comp
      (Algebra.linearMap U.ring (Crystalline.DividedCoordinates.object U σ).ring)

theorem constantsLinear_apply (U : BigCrystallineSite.Object p B J δ f) (a : U.ring) :
    constantsLinear σ U a = CoordinatesDeRham.constants σ U a := rfl

def augmentationZero : BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) f ⟶
    CoordinatesModuleMaps.formsPresheaf σ 0 where
  app U := ModuleCat.ofHom
    (X := (BigCrystallineCohomology.modulePresheaf f).obj U)
    (Y := CoordinatesModuleMaps.formsModule σ U.unop 0)
    { toFun := constantsLinear σ U.unop
      map_add' := (constantsLinear σ U.unop).map_add
      map_smul' := fun b a => (constantsLinear σ U.unop).map_smul (U.unop.base b) a }
  naturality _ _ α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (CoordinatesDeRham.constants_natural σ α.unop a).symm

theorem augmentationZero_differential :
    augmentationZero (p := p) (B := B) (J := J) (δ := δ) (f := f) σ ≫ differential σ 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact CoordinatesDeRham.constants_differential σ U.unop a

def augmentation :
    (CochainComplex.single₀ ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ ModuleCat.{u} B)).obj
      (BigCrystallineCohomology.modulePresheaf f) ⟶ complex σ :=
  (CochainComplex.fromSingle₀Equiv (complex σ) (BigCrystallineCohomology.modulePresheaf f)).symm
    ⟨augmentationZero σ, by rw [complex_d]; exact augmentationZero_differential σ⟩

theorem augmentation_zero :
    (augmentation (p := p) (B := B) (J := J) (δ := δ) (f := f) σ).f 0 = augmentationZero σ :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesModuleComplex
