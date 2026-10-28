import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.ScalarNaturality

/-! # Relative Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms.BigCrystallineRelativeForms

noncomputable section

/-! # The original big frame resolution as actual relative PD forms -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)}
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor.BigCrystallineFrameFunctor.functions (p := p) (J := J) (δ := δ) (base := base) a
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators.BigCrystallineFrameOperators.derivative (p := p) (J := J) (δ := δ) (base := base) a
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.functor W σ F D (OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.commute a)

def object (Q : Cᵒᵖ) : CochainComplex (ModuleCat W) ℕ :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (algebraMap W Q.unop.ring)
    (PD.DeRham.PDDeRham.complex Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers))

def objectIso (Q : Cᵒᵖ) : (K).obj Q ≅ object (σ := σ) Q :=
  FreeRelative.ScalarComparison.FreeRelativeScalarComparison.complexIso W Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers

def map {Q P : Cᵒᵖ} (f : Q ⟶ P) : object (σ := σ) Q ⟶ object (σ := σ) P :=
  PD.RelativeScalarMap.PDRelativeScalarMap.complexMap W Q.unop.ring P.unop.ring
    (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (DividedPowerAlgebra P.unop.ring (σ →₀ P.unop.ring))
    f.unop.ringMap.toRingHom (fun w => DFunLike.congr_fun f.unop.overBase w)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap a f.unop).toRingHom
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a f.unop)
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal P.unop.ring σ P.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers P.unop.ring σ P.unop.ideal P.unop.dividedPowers)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a f.unop)

theorem square {Q P : Cᵒᵖ} (f : Q ⟶ P) :
    (K).map f ≫ (objectIso a P).hom = (objectIso a Q).hom ≫ BigCrystallineRelativeForms.map a f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact (FreeRelative.ScalarNaturality.FreeRelativeScalarNaturality.component W Q.unop.ring P.unop.ring σ
    Q.unop.ideal Q.unop.dividedPowers P.unop.ideal P.unop.dividedPowers
    f.unop.ringMap.toRingHom (fun w => DFunLike.congr_fun f.unop.overBase w)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap a f.unop)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a f.unop)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a f.unop)
    (FrameLifts.BigCrystallineFrameLifts.translation a f.unop)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate a f.unop) n).symm

def functor : Cᵒᵖ ⥤ CochainComplex (ModuleCat W) ℕ where
  obj := object (σ := σ)
  map := BigCrystallineRelativeForms.map a
  map_id Q := by
    apply (cancel_epi (objectIso a Q).hom).mp
    rw [← square, (K).map_id, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply (cancel_epi (objectIso a _).hom).mp
    rw [← square, (K).map_comp, Category.assoc, square, ← Category.assoc, square, Category.assoc]

def iso : K ≅ functor a := NatIso.ofComponents (objectIso a) (square a)

def complex : CochainComplex (Cᵒᵖ ⥤ ModuleCat W) ℕ :=
  ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (functor a)

def complexIso : FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a ≅
    complex (p := p) (J := J) (δ := δ) (base := base) a :=
  (ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).mapIso (iso a)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms.BigCrystallineRelativeForms
