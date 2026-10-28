import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FinitePELHomeomorph
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteAway
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalOpen

/-! # Away PEL Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPELLevel.Approximation

noncomputable section

/-! The away level is the inverse image of the literal PEL principal
subgroup under insertion of the identity at the selected local factor. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open _root_.Module

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

def cmOriginalPELHomeomorph : FiniteAway.Approximation.CMFiniteSU E P hP ≃ₜ* P.FiniteSpecialUnitary :=
  FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P hP.2.1 hP.2.2.1

variable (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E))

def cmAwayToPEL : FiniteAway.Approximation.CMFiniteAway E P hP w →ₜ* P.FiniteSpecialUnitary where
  toMonoidHom := (cmOriginalPELHomeomorph E P hP).toMulEquiv.toMonoidHom.comp
    (RestrictedInsert.Approximation.restrictedInsertPlace _ w)
  continuous_toFun := (cmOriginalPELHomeomorph E P hP).continuous.comp
    (RestrictedInsert.Approximation.restrictedInsertPlace_continuous _ w)

variable {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ P.lattice] (b : Basis J ℤ P.lattice)

def cmAwayPELLevel (N : ℕ) (hN : 0 < N) : OpenSubgroup (FiniteAway.Approximation.CMFiniteAway E P hP w) :=
  (PEL.PrincipalOpen.Approximation.pelPrincipalOpenSubgroup E P b N hN).comap (cmAwayToPEL E P hP w).toMonoidHom
    (cmAwayToPEL E P hP w).continuous

theorem cmAwayPELLevel_mem (N : ℕ) (hN : 0 < N) (g : FiniteAway.Approximation.CMFiniteAway E P hP w) :
    g ∈ cmAwayPELLevel E P hP w b N hN ↔ cmAwayToPEL E P hP w g ∈ P.adelicPrincipalLevel N := Iff.rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPELLevel.Approximation
