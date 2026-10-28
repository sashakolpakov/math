import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PointedLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplement

/-! # Parameter Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Every complex point of an actual finite parameter scheme over a number
field descends, with the specified embedding and an explicit comparison
morphism. Finiteness proves the needed bound on parameter points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

def Base.ArithmeticBaseExtension.complexFieldMap (B : Base.ArithmeticBaseExtension K κ) :
    Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ Over.mk B.fieldExtension :=
  Over.homMk (Spec.map (CommRingCat.ofHom B.embedding)) (by
    change Spec.map (CommRingCat.ofHom B.embedding) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B.extension.carrier)) = _
    rw [← Spec.map_comp]
    exact congrArg (fun r : K →+* ℂ => Spec.map (CommRingCat.ofHom r)) B.embedding_extends)

/-- Actual finite parameter schemes have effective finite-extension points;
neither arithmetic isolation nor a descended point is assumed. -/
theorem Finite.ParameterDescent.finite_parameter_descends (κ : K →+* ℂ)
    (P : Over (Spec (.of K))) [IsFinite P.hom]
    (p : Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ P) (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ) (pL : Over.mk B.fieldExtension ⟶ P),
      B.denominator = N ∧ B.complexFieldMap ≫ pL = p := by
  let PC := (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj P
  have : IsFinite PC.hom := inferInstanceAs
    (IsFinite (pullback.snd P.hom (Spec.map (CommRingCat.ofHom κ))))
  have : Finite (CountableParameters.ParameterPoints PC) := IsogenyComplement.finite_parameterPoints PC
  let e := Arithmetic.PointedLifts.fiberParameterPointsEquiv (Spec.map (CommRingCat.ofHom κ)) P
  obtain ⟨B, pL, hBN, hpL, hfactor⟩ := Arithmetic.Parameters.parameter_finite_extension_of_countable_fiber κ P
    (e.symm p) N hN
  refine ⟨B, Over.homMk pL hpL, hBN, ?_⟩
  apply Over.OverMorphism.ext
  exact hfactor.trans (congrArg Over.Hom.left (e.apply_symm_apply p))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
