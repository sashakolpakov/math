import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.UniversalFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ParameterQuasiProjectivity

/-! # Factorization Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationProjection

noncomputable section

/-! The universal closed factorization has an actual projection to any proper target family, over its closed parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z : Over M.left}
variable [IsProper X.hom] [Flat X.hom] (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P)

abbrev factorizationSource : Over (Proper.FactorizationParameter.properFactorizationParameter M j i).left :=
  (Over.pullback (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj X

abbrev factorizationTarget (A : Over M.left) : Over (Proper.FactorizationParameter.properFactorizationParameter M j i).left :=
  (Over.pullback (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj A

def factorizationProjection {A : Over M.left} (p : Z ⟶ A) :
    factorizationSource M j i ⟶ factorizationTarget M j i A :=
  Proper.UniversalFactorization.properUniversalFactorization M j i ≫
    (Over.pullback (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).map p

instance factorizationSource_proper : IsProper (factorizationSource M j i).hom :=
  inferInstanceAs (IsProper (Limits.pullback.snd X.hom (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left))

instance factorizationSource_flat : Flat (factorizationSource M j i).hom :=
  inferInstanceAs (Flat (Limits.pullback.snd X.hom (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left))

instance factorizationTarget_proper (A : Over M.left) [IsProper A.hom] :
    IsProper (factorizationTarget M j i A).hom :=
  inferInstanceAs (IsProper (Limits.pullback.snd A.hom (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left))

theorem factorizationParameter_locallyNoetherian :
    IsLocallyNoetherian (Proper.FactorizationParameter.properFactorizationParameter M j i).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left

theorem factorizationTarget_locallyNoetherian (A : Over M.left) [IsProper A.hom] :
    IsLocallyNoetherian (factorizationTarget M j i A).left := by
  have : IsLocallyNoetherian (Proper.FactorizationParameter.properFactorizationParameter M j i).left :=
    factorizationParameter_locallyNoetherian M j i
  exact LocallyOfFiniteType.isLocallyNoetherian (factorizationTarget M j i A).hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationProjection
