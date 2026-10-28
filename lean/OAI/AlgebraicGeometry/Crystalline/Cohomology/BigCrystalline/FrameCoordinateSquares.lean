import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerForms

/-! # Frame Coordinate Squares -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameCoordinateSquares.BigCrystallineFrameCoordinateSquares

noncomputable section

/-! # The original twist and power maps in relative differential-form coordinates -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  {σ : Type u} (a : σ → A) [Fintype σ] [LinearOrder σ]

theorem restriction
    {Q P : (FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base)ᵒᵖ} (f : Q ⟶ P) (j : ℕ)
    (z : ((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X j).obj Q) :
    ((RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base) a).hom.f j).app P
      (((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X j).map f z) =
    (RelativeForms.BigCrystallineRelativeForms.map a f).f j
      (((RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base) a).hom.f j).app Q z) := by
  have hs := congrArg (fun f => f.f j) (RelativeForms.BigCrystallineRelativeForms.square a f)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hs) z

theorem power (m : ℕ) :
    PowerForms.BigCrystallinePowerForms.complexMap (p := p) (J := J) (δ := δ) (base := base) a m ≫
      (RelativeForms.BigCrystallineRelativeForms.complexIso a).hom =
    (RelativeForms.BigCrystallineRelativeForms.complexIso (fun i => a i ^ m)).hom ≫
      PowerForms.BigCrystallinePowerForms.relativeComplexMap a m := by
  unfold PowerForms.BigCrystallinePowerForms.complexMap
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

theorem twist :
    (TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a).hom ≫
      (RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base) a).hom =
    ((TwistResolution.BigCrystallineTwistResolution.restriction p W A J δ base base' e he h).mapHomologicalComplex (.up ℕ)).map
        (RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base') a).hom ≫
      (TwistResolution.BigCrystallineTwistResolution.relativeIso p W A J δ base base' e he h a).hom := by
  unfold TwistResolution.BigCrystallineTwistResolution.iso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameCoordinateSquares.BigCrystallineFrameCoordinateSquares
