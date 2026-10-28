import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Morphism Equality Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityParameters

noncomputable section

/-! Equality of universal proper-flat family morphisms is represented by a specified closed parameter scheme, retaining quasi-projectivity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X Y : Over M.left}
variable [IsProper X.hom] [Flat X.hom] [IsSeparated Y.hom] (u v : X ⟶ Y)

def properMorphismEqualityParameter : Over S := Closed.IdealParameter.closedIdealParameter M (MorphismEqualityIdeal.properMorphismEqualityIdeal u v)

def properMorphismEqualityParameterInclusion : properMorphismEqualityParameter M u v ⟶ M :=
  Closed.IdealParameter.closedIdealParameterInclusion M (MorphismEqualityIdeal.properMorphismEqualityIdeal u v)

instance properMorphismEqualityParameterInclusion_closed :
    IsClosedImmersion (properMorphismEqualityParameterInclusion M u v).left :=
  Closed.IdealParameter.closedIdealParameterInclusion_closed M (MorphismEqualityIdeal.properMorphismEqualityIdeal u v)

def properMorphismEqualityParameterPointEquiv (T : Over S) :
    (T ⟶ properMorphismEqualityParameter M u v) ≃
      {c : T ⟶ M // (Over.pullback c.left).map u = (Over.pullback c.left).map v} :=
  (Closed.IdealParameter.closedIdealParameterPointEquiv M (MorphismEqualityIdeal.properMorphismEqualityIdeal u v) T).trans
    { toFun := fun c => ⟨c.val, (MorphismEqualityIdeal.properMorphismEqualityIdeal_test u v c.val.left).mp c.property⟩
      invFun := fun c => ⟨c.val, (MorphismEqualityIdeal.properMorphismEqualityIdeal_test u v c.val.left).mpr c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

theorem properMorphismEqualityParameter_universal :
    (Over.pullback (properMorphismEqualityParameterInclusion M u v).left).map u =
      (Over.pullback (properMorphismEqualityParameterInclusion M u v).left).map v := by
  apply (MorphismEqualityIdeal.properMorphismEqualityIdeal_test u v (properMorphismEqualityParameterInclusion M u v).left).mp
  change (MorphismEqualityIdeal.properMorphismEqualityIdeal u v).comap (MorphismEqualityIdeal.properMorphismEqualityIdeal u v).subschemeι = ⊥
  rw [Closed.ConditionIdeals.ideal_comap_eq_bot_iff, Scheme.IdealSheafData.ker_subschemeι]

def properMorphismEqualityParameterQuasiProjectivePresentation [IsNoetherian S]
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) : Projective.ProjectivePresentations.QuasiProjectivePresentation (properMorphismEqualityParameter M u v) :=
  Q.ofClosedImmersion (properMorphismEqualityParameterInclusion M u v)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityParameters
