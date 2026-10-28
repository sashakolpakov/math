/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistTransitions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomOverlapGluing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateCompatibleExtensions

/-! # Negative Twist Maps -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps

noncomputable section

open _root_.MvPolynomial

/-! Maps from negative twists, constructed by gluing actual local module maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
namespace MvPolynomial
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateHyperplaneIdealModulePowerOverFrame (i j : σ) (n : ℕ) :=
  Invertible.Scheme.Modules.overTrivializationOfRestrictIso
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) i j n)

def coordinateHyperplaneIdealModulePowerFrameSection (i j : σ) (n : ℕ) :
    Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
  FrameSections.overTrivializationSection (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (coordinateHyperplaneIdealModulePowerOverFrame i j n) 1

theorem coordinateHyperplaneIdealModulePowerOverFrame_transition (i k j : σ) (n : ℕ) :
    let X := Proj (homogeneousSubmodule σ R)
    let N := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n
    let W := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
    (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k) (coordinateHyperplaneIdealModulePowerOverFrame k j n)
      (Over.mk (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)))).hom =
    (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (coordinateHyperplaneIdealModulePowerOverFrame i j n)
      (Over.mk (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)))).hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W
        ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k : Γ(X, W)) ^ n) := by
  let N := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n
  let W := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
  let a := OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) i j n)
  let b := OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) k j n)
  let r : Γ(Proj (homogeneousSubmodule σ R), W) := CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k
  have hp : b.hom = a.hom ≫ UnitScalar.unitEndomorphismOfTopSection
      (OpenFrames.Scheme.Modules.openTopSection W (r ^ n)) := by
    simpa only [OpenFrames.Scheme.Modules.openTopSection, map_pow] using
      NegativeTwistTransitions.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization_restrict_transition (R := R) i k j n
  have h := OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar N W b a (r ^ n) hp
  dsimp only [a, b] at h
  rw [OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization,
    OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization] at h
  exact h

theorem exists_coordinateNegativeTwistHom_of_coefficients
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (n : ℕ)
    (t : ∀ i : σ, Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i))
    (ht : ∀ i k : σ,
      M.presheaf.map (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op (t i) =
      (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
        Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) ^ n •
        M.presheaf.map (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)).op (t k)) :
    ∃ f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n ⟶ M,
      ∀ i, f.val.app (.op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i))
        (coordinateHyperplaneIdealModulePowerFrameSection (R := R) i j n) = t i := by
  let X := Proj (homogeneousSubmodule σ R)
  let N := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n
  let U : σ → X.Opens := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R)
  let W : σ → σ → X.Opens := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R)
  let e := fun i => coordinateHyperplaneIdealModulePowerOverFrame (R := R) i j n
  let f := fun i => FramedLocalHom.framedLocalHom N M (U i) (e i) (t i)
  have hf (i k : σ) :
      LinearHom.linearHomRestrict X.ringCatSheaf N M
        (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op (f i) =
      LinearHom.linearHomRestrict X.ringCatSheaf N M
        (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)).op (f k) := by
    dsimp only [f]
    rw [FramedLocalHom.framedLocalHom_restrict, FramedLocalHom.framedLocalHom_restrict]
    exact FramedLocalHom.framedLocalHom_eq_of_transition N M (W i k) _ _
      ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k : Γ(X, W i k)) ^ n) _ _
      (coordinateHyperplaneIdealModulePowerOverFrame_transition (R := R) i k j n) (ht i k)
  obtain ⟨g, hg⟩ := ModuleHomOverlapGluing.exists_moduleHom_of_overlap_localMaps N M U
    (MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := R)) W
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R)) (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R))
    (fun i k => by dsimp only [U, W]; rw [CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]) f hf
  refine ⟨g, fun i => ?_⟩
  have hi := congrArg
    (fun q => q.val.app (.op (Over.mk (𝟙 (U i))))
      (coordinateHyperplaneIdealModulePowerFrameSection (R := R) i j n)) (hg i)
  exact hi.trans (FramedLocalHom.framedLocalHom_apply_frame N M (U i) (e i) (t i))

/-- Every chart section is the image of the standard frame under a map from
some actual negative twist. -/
theorem exists_coordinateNegativeTwistHom_frameSection_eq [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (s : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    ∃ (n : ℕ) (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n ⟶ M),
      f.val.app (.op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
        (coordinateHyperplaneIdealModulePowerFrameSection (R := R) j j n) = s := by
  obtain ⟨n, t, hj, ht⟩ := CoordinateCompatibleExtensions.MvPolynomial.exists_compatible_coordinateCoefficients M j s
  obtain ⟨f, hf⟩ := exists_coordinateNegativeTwistHom_of_coefficients M j n t ht
  exact ⟨n, f, (hf j).trans hj⟩

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps
