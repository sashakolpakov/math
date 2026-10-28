import OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.PoincareAugmentationFormula
import Mathlib.Algebra.Homology.Functor

/-! # Coordinates De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesDeRham

noncomputable section

/-!
# IntegralComparison: the augmented relative de Rham complex on the original crystalline site

The actual divided-coordinate form presheaves and differentials assemble
into a complex. The original ambient functions map naturally into its
degree-zero cycles by the canonical inclusion of constants.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesForms

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (σ : Type u)

def differential (n : ℕ) :
    CoordinatesForms.formsPresheaf (p := p) (B := B) (J := J) (δ := δ) (f := f) σ n ⟶ CoordinatesForms.formsPresheaf σ (n + 1) where
  app U := AddCommGrpCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential U.unop.ring (Crystalline.DividedCoordinates.object U.unop σ).ring
    (Crystalline.DividedCoordinates.object U.unop σ).ideal (Crystalline.DividedCoordinates.object U.unop σ).dividedPowers n).toAddMonoidHom
  naturality _ _ α := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro ω
    exact (CoordinatesForms.formsMap_differential σ α.unop n ω).symm

theorem differential_square (n : ℕ) :
    differential (p := p) (B := B) (J := J) (δ := δ) (f := f) σ n ≫ differential σ (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro ω
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential_square U.unop.ring (Crystalline.DividedCoordinates.object U.unop σ).ring
    (Crystalline.DividedCoordinates.object U.unop σ).ideal (Crystalline.DividedCoordinates.object U.unop σ).dividedPowers n ω

def complex : CochainComplex ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (CoordinatesForms.formsPresheaf σ) (differential σ) (differential_square σ)

theorem complex_d (n : ℕ) :
    (complex (p := p) (B := B) (J := J) (δ := δ) (f := f) σ).d n (n + 1) = differential σ n :=
  CochainComplex.of_d _ _ n

def ambientPresheaf : (BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of U.unop.ring
  map α := AddCommGrpCat.ofHom α.unop.ringMap.toRingHom.toAddMonoidHom
  map_id _U := rfl
  map_comp _α _β := rfl

def constants (U : BigCrystallineSite.Object p B J δ f) : U.ring →+ CoordinatesForms.Forms σ U 0 :=
  (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv U.ring (Crystalline.DividedCoordinates.object U σ).ring (Crystalline.DividedCoordinates.object U σ).ideal
    (Crystalline.DividedCoordinates.object U σ).dividedPowers).symm.toAddEquiv.toAddMonoidHom.comp
      (algebraMap U.ring (Crystalline.DividedCoordinates.object U σ).ring).toAddMonoidHom

theorem constants_symbol (U : BigCrystallineSite.Object p B J δ f) (a : U.ring) :
    constants σ U a = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol U.ring (Crystalline.DividedCoordinates.object U σ).ring (Crystalline.DividedCoordinates.object U σ).ideal
      (Crystalline.DividedCoordinates.object U σ).dividedPowers (algebraMap U.ring (Crystalline.DividedCoordinates.object U σ).ring a) (fun i : Fin 0 => i.elim0) := by
  apply (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv U.ring (Crystalline.DividedCoordinates.object U σ).ring (Crystalline.DividedCoordinates.object U σ).ideal
    (Crystalline.DividedCoordinates.object U σ).dividedPowers).injective
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.degreeZeroEquiv_symbol]
  exact LinearEquiv.apply_symm_apply _ _

theorem constants_natural {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) (a : V.ring) :
    CoordinatesForms.formsMap σ α 0 (constants σ V a) = constants σ U (α.ringMap a) := by
  rw [constants_symbol, CoordinatesForms.formsMap_symbol, constants_symbol,
    CoordinatesFunctor.ringMap_coefficient]
  congr 1
  funext i
  exact i.elim0

theorem constants_differential (U : BigCrystallineSite.Object p B J δ f) (a : U.ring) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential U.ring (Crystalline.DividedCoordinates.object U σ).ring (Crystalline.DividedCoordinates.object U σ).ideal
      (Crystalline.DividedCoordinates.object U σ).dividedPowers 0 (constants σ U a) = 0 := by
  rw [constants_symbol, AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor.PDDeRhamTensor.differential_symbol]
  unfold AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol
  have h := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_base U.ring (Crystalline.DividedCoordinates.object U σ).ring
    (Fin.cons 0 (fun i : Fin 0 => i.elim0)) 0 a
  rw [Fin.update_cons_zero] at h
  rw [h, map_zero]

def augmentationZero : ambientPresheaf (p := p) (B := B) (J := J) (δ := δ) (f := f) ⟶ CoordinatesForms.formsPresheaf σ 0 where
  app U := AddCommGrpCat.ofHom (constants σ U.unop)
  naturality _ _ α := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun a => (constants_natural σ α.unop a).symm)

theorem augmentationZero_differential :
    augmentationZero (p := p) (B := B) (J := J) (δ := δ) (f := f) σ ≫ differential σ 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (constants_differential σ U.unop)

def augmentation :
    (CochainComplex.single₀ ((BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj ambientPresheaf ⟶ complex σ :=
  (CochainComplex.fromSingle₀Equiv (complex σ) ambientPresheaf).symm
    ⟨augmentationZero σ, by
      change augmentationZero σ ≫ (complex σ).d 0 1 = 0
      rw [complex_d]
      exact augmentationZero_differential σ⟩

theorem augmentation_zero :
    (augmentation (p := p) (B := B) (J := J) (δ := δ) (f := f) σ).f 0 = augmentationZero σ :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Divided.CoordinatesDeRham
