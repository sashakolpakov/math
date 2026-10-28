import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameCoordinateSquares
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ScalarSquareEvaluation

/-! # Twist Coordinate Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistCoordinateForms.BigCrystallineTwistCoordinateForms

noncomputable section

/-! # The original inverse-coefficient twist is the identity on raw relative-form coordinates -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  {σ : Type u} (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base') a
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base) a
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base') a

theorem component (Q : Cᵒᵖ) (j : ℕ) :
    ((TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a).hom.f j).app Q =
      (ModuleCat.restrictScalars e.symm.toRingHom).map (((d).hom.f j).app ((ι).op.obj Q)) ≫
        ((TwistResolution.BigCrystallineTwistResolution.relativeIso p W A J δ base base' e he h a).hom.f j).app Q ≫
          ((c).inv.f j).app Q :=
  ComplexAssemblyTrans.ComplexAssemblyConjugation.component (ι).op (ModuleCat.restrictScalars e.symm.toRingHom) (.up ℕ)
    d (TwistResolution.BigCrystallineTwistResolution.relativeIso p W A J δ base base' e he h a) c j Q

theorem square_component (Q : Cᵒᵖ) (j : ℕ) :
    ((TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a).hom.f j).app Q ≫ ((c).hom.f j).app Q =
      (ModuleCat.restrictScalars e.symm.toRingHom).map (((d).hom.f j).app ((ι).op.obj Q)) ≫
        ((TwistResolution.BigCrystallineTwistResolution.relativeIso p W A J δ base base' e he h a).hom.f j).app Q :=
  congrArg (fun f => (f.f j).app Q)
    (FrameCoordinateSquares.BigCrystallineFrameCoordinateSquares.twist p W A J δ base a base' e he h)

abbrev Form (Q : Cᵒᵖ) (j : ℕ) :=
  PD.DeRham.PDDeRham.Form Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers) j

def targetMap (Q : Cᵒᵖ) (j : ℕ) :
    ((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X j).obj Q →+
      Form p W A J δ base (σ := σ) Q j :=
  (((c).hom.f j).app Q).hom.toAddMonoidHom

def sourceMap (Q : Cᵒᵖ) (j : ℕ) : ((K).X j).obj ((ι).op.obj Q) →+
    Form p W A J δ base (σ := σ) Q j :=
  (((d).hom.f j).app ((ι).op.obj Q)).hom.toAddMonoidHom

def twistHom (Q : Cᵒᵖ) (j : ℕ) :
    (ModuleCat.restrictScalars e.symm.toRingHom).obj (((K).X j).obj ((ι).op.obj Q)) ⟶
      ((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X j).obj Q :=
  ((TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a).hom.f j).app Q

def twistMap (Q : Cᵒᵖ) (j : ℕ) : ((K).X j).obj ((ι).op.obj Q) →+
    ((FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X j).obj Q :=
  ScalarRestricted.ScalarRestrictedAdditiveMap.map e.symm.toRingHom (twistHom p W A J δ base base' e he h a Q j)

def relativeMap (Q : Cᵒᵖ) (j : ℕ) : Form p W A J δ base (σ := σ) Q j →+
    Form p W A J δ base (σ := σ) Q j :=
  (((TwistResolution.BigCrystallineTwistResolution.relativeIso p W A J δ base base' e he h a).hom.f j).app Q).hom.toAddMonoidHom

theorem relativeMap_id (Q : Cᵒᵖ) (j : ℕ) : relativeMap p W A J δ base base' e he h a Q j = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro ω
  exact TwistResolution.BigCrystallineTwistResolution.relative_apply p W A J δ base base' e he h a Q j ω

theorem additive_square (Q : Cᵒᵖ) (j : ℕ) :
    (targetMap p W A J δ base a Q j).comp (twistMap p W A J δ base base' e he h a Q j) =
      (relativeMap p W A J δ base base' e he h a Q j).comp (sourceMap p W A J δ base base' e he h a Q j) :=
  Module.ScalarSquareEvaluation.ModuleScalarSquareEvaluation.addHom e.symm.toRingHom
    (((d).hom.f j).app ((ι).op.obj Q))
    (twistHom p W A J δ base base' e he h a Q j)
    (((c).hom.f j).app Q)
    (((TwistResolution.BigCrystallineTwistResolution.relativeIso p W A J δ base base' e he h a).hom.f j).app Q)
    (square_component p W A J δ base base' e he h a Q j)

theorem coordinates (Q : Cᵒᵖ) (j : ℕ) (z : ((K).X j).obj ((ι).op.obj Q)) :
    targetMap p W A J δ base a Q j (twistMap p W A J δ base base' e he h a Q j z) =
      sourceMap p W A J δ base base' e he h a Q j z := by
  have hs := additive_square p W A J δ base base' e he h a Q j
  rw [relativeMap_id, AddMonoidHom.id_comp] at hs
  exact DFunLike.congr_fun hs z

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistCoordinateForms.BigCrystallineTwistCoordinateForms
