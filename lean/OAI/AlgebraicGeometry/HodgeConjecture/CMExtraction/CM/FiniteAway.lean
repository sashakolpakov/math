import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedAwaySame
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary

/-! # Finite Away -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteAway.Approximation

noncomputable section

/-! The original rational CM unitary group in its actual finite local
unitary groups, with one specified factor removed. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary.Quadratic OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneTheta.Multiplicity

theorem finiteSUAway_topologicalGroup
    (F : Type) [Field F] [NumberField F] {d : F} {n : ℕ}
    (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    IsTopologicalGroup (RestrictedAwaySame.Approximation.RestrictedAway
      (fun z : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr z)) w) := by
  let : Fact (∀ z : {z : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F // z ≠ w},
      IsOpen (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr z.val) :
        Set (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr z.val))))) :=
    ⟨fun z => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral_open F H.val (.inr z.val)⟩
  infer_instance

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

abbrev CMFiniteSU := RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)

def cmRationalFiniteSU : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b →* CMFiniteSU E P hP :=
  (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)).comp
    (Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
      (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1).toMonoidHom

abbrev CMFiniteAway (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E)) :=
  RestrictedAwaySame.Approximation.RestrictedAway (fun z : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E) =>
    RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP).val (.inr z)) w

def cmForgetPlace (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E)) :
    CMFiniteSU E P hP →ₜ* CMFiniteAway E P hP w :=
  RestrictedAwaySame.Approximation.restrictedForgetPlaceContinuous _ w

def cmRationalFiniteAway (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E)) :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b →* CMFiniteAway E P hP w :=
  (cmForgetPlace E P hP w).toMonoidHom.comp (cmRationalFiniteSU E P hP)

theorem cmFiniteAway_topologicalGroup (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E)) :
    IsTopologicalGroup (CMFiniteAway E P hP w) :=
  finiteSUAway_topologicalGroup (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) w

theorem cmRationalFiniteSU_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E)) :
    (cmRationalFiniteSU E P hP g w).val.val =
      g.val.val.map ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneParameter E P hP)
        (.inr w)).comp (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E P.imaginaryScalar
          (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP)).symm.toRingHom) := rfl

theorem cmRationalFiniteAway_apply (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E) // z ≠ w}) :
    cmRationalFiniteAway E P hP w g z = cmRationalFiniteSU E P hP g z.val := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteAway.Approximation
