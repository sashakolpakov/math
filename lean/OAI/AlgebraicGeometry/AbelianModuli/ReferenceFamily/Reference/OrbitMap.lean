import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Points
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallOrbitQuotient

/-! # Orbit Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual reference moduli points are invariant under the literal
principal arithmetic action, so they define a map from its orbit quotient. -/

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (he : κ.comp iota = P.μ)

theorem Models.FinePELModel.referencePoint_principal (g : Groups.principalSpecialUnitary P.b P.lattice N) (z : P.Domain) :
    M.referencePoint hM κ hP he (g • z) = M.referencePoint hM κ hP he z :=
  (M.referencePoint_eq_iff hM κ hP he (g • z) z).mpr
    ⟨(P.referencePELObject_principal_iso hP iota κ he N g z).symm⟩

theorem Models.FinePELModel.referencePoint_orbit {z w : P.Domain} (h : (P.principalOrbitSetoid N).r z w) :
    M.referencePoint hM κ hP he z = M.referencePoint hM κ hP he w := by
  obtain ⟨g, hg⟩ := (show ∃ g : Groups.principalSpecialUnitary P.b P.lattice N, g • w = z from h)
  rw [← hg]
  exact M.referencePoint_principal hM κ hP he g w

def Models.FinePELModel.referenceOrbitMap : Quotient (P.principalOrbitSetoid N) → M.ComplexPoints κ :=
  Quotient.lift (M.referencePoint hM κ hP he) (fun _ _ h => M.referencePoint_orbit hM κ hP he h)

theorem Models.FinePELModel.referenceOrbitMap_projection (z : P.Domain) :
    M.referenceOrbitMap hM κ hP he (P.principalOrbitProjection N z) = M.referencePoint hM κ hP he z := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
