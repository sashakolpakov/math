import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionToInjective

/-! # Resolution Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionMap

noncomputable section

/-! Arbitrary geometric pullback maps between the original bounded crystalline resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (IY : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  (IX : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n))

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (p := p) (J := J) (δ := δ) g hg n

def complex := ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj IY.cocomplex

def augmentation : (CochainComplex.single₀ _).obj
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n) ⟶
      complex g hg n IY :=
  Single.ComplexTransport.map F s IY.ι

instance augmentation_quasiIso : QuasiIso (augmentation g hg n IY) := by
  let : QuasiIso IY.ι := IY.quasiIso
  let : (Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n).PreservesHomology := by
    infer_instance
  have hφ : QuasiIso (((F).mapHomologicalComplex (ComplexShape.up ℕ)).map IY.ι) := by infer_instance
  have hψ : QuasiIso (Single.ComplexTransport.sourceIso F s).inv := by infer_instance
  exact quasiIso_comp (Single.ComplexTransport.sourceIso F s).inv
    (((F).mapHomologicalComplex (ComplexShape.up ℕ)).map IY.ι) (hφ := hψ) (hφ' := hφ)

def map : complex g hg n IY ⟶ IX.cocomplex :=
  Augmented.ResolutionToInjective.map (complex g hg n IY) (augmentation g hg n IY) IX (𝟙 _)

theorem map_augmentation : augmentation g hg n IY ≫ ResolutionMap.map g hg n IY IX = IX.ι :=
  (Augmented.ResolutionToInjective.augmentation (complex g hg n IY)
    (augmentation g hg n IY) IX (𝟙 _)).trans
      ((congrArg (fun a => a ≫ IX.ι) ((CochainComplex.single₀ _).map_id _)).trans (Category.id_comp _))

theorem augmentation_zero : (augmentation g hg n IY).f 0 = (s).inv ≫ (F).map (IY.ι.f 0) :=
  Single.ComplexTransport.map_zero F s IY.ι

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionMap
