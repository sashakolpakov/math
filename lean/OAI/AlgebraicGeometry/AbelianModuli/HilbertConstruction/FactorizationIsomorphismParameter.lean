import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationProjection

/-! # Factorization Isomorphism Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationIsomorphismParameter

noncomputable section

/-! Closed factorization followed by isomorphism of the resulting projection is represented by an actual open subscheme of the closed parameter locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z A : Over M.left}
variable [IsProper X.hom] [Flat X.hom] [IsProper A.hom]
variable (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P) (p : Z ⟶ A)

def factorizationIsomorphismParameter : Over S :=
  IsomorphismOpenParameters.isomorphismOpenParameter (Proper.FactorizationParameter.properFactorizationParameter M j i) (FactorizationProjection.factorizationProjection M j i p)

def factorizationIsomorphismParameterInclusion :
    factorizationIsomorphismParameter M j i p ⟶ Proper.FactorizationParameter.properFactorizationParameter M j i :=
  Open.ParameterPoints.openParameterInclusion (Proper.FactorizationParameter.properFactorizationParameter M j i)
    (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen (FactorizationProjection.factorizationProjection M j i p))

instance factorizationIsomorphismParameterInclusion_open :
    IsOpenImmersion (factorizationIsomorphismParameterInclusion M j i p).left :=
  inferInstanceAs (IsOpenImmersion
    (Open.ParameterPoints.openParameterInclusion (Proper.FactorizationParameter.properFactorizationParameter M j i)
      (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen (FactorizationProjection.factorizationProjection M j i p))).left)

def factorizationIsomorphismParameterPointEquiv (T : Over S) :
    (T ⟶ factorizationIsomorphismParameter M j i p) ≃
      {c : T ⟶ Proper.FactorizationParameter.properFactorizationParameter M j i //
        IsIso ((Over.pullback c.left).map (FactorizationProjection.factorizationProjection M j i p))} := by
  letI : IsLocallyNoetherian (FactorizationProjection.factorizationTarget M j i A).left :=
    FactorizationProjection.factorizationTarget_locallyNoetherian M j i A
  exact IsomorphismOpenParameters.isomorphismOpenParameterPointEquiv (Proper.FactorizationParameter.properFactorizationParameter M j i)
    (FactorizationProjection.factorizationProjection M j i p) T

theorem factorizationIsomorphismParameter_universal_isIso :
    IsIso ((Over.pullback (factorizationIsomorphismParameterInclusion M j i p).left).map
      (FactorizationProjection.factorizationProjection M j i p)) := by
  have : IsLocallyNoetherian (FactorizationProjection.factorizationTarget M j i A).left :=
    FactorizationProjection.factorizationTarget_locallyNoetherian M j i A
  apply (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen_pullback_iff (FactorizationProjection.factorizationProjection M j i p)
    (factorizationIsomorphismParameterInclusion M j i p).left).mpr
  rintro _ ⟨t, rfl⟩
  exact t.property

def factorizationIsomorphismParameterQuasiProjectivePresentation [IsNoetherian S]
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (factorizationIsomorphismParameter M j i p) :=
  Proper.ParameterQuasiProjectivity.isomorphismOpenParameterQuasiProjectivePresentation (Proper.FactorizationParameter.properFactorizationParameter M j i)
    (Proper.ParameterQuasiProjectivity.properFactorizationParameterQuasiProjectivePresentation M Q j i) (FactorizationProjection.factorizationProjection M j i p)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationIsomorphismParameter
