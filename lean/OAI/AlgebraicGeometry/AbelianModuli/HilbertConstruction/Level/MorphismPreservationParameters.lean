import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PullbackPreservationCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme

/-! # Morphism Preservation Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.MorphismPreservationParameters

noncomputable section

/-! Full-level preservation by a family morphism is represented by a specified closed parameter scheme, with its exact all-test-scheme condition and a quasi-projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
variable {g N : ℕ} [NeZero N] (A B : Abelian.Schemes.AbelianScheme g M.left)
variable (l : A.FullLevel N) (k : B.FullLevel N) (f : A.scheme ⟶ B.scheme)

local instance fullLevelConstant_proper : IsProper (Level.Scheme.constantFullLevelScheme g N M.left).hom :=
  Finite.ConstantScheme.constantScheme_proper

local instance fullLevelConstant_flat : Flat (Level.Scheme.constantFullLevelScheme g N M.left).hom := by
  have : Etale (Level.Scheme.constantFullLevelScheme g N M.left).hom := Level.Scheme.constantScheme_etale _ _
  infer_instance

def fullLevelMorphismPreservingParameter : Over S :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameter M (l.schemeIso.hom ≫ A.torsionInclusion N ≫ f)
    (k.schemeIso.hom ≫ B.torsionInclusion N)

def fullLevelMorphismPreservingParameterInclusion : fullLevelMorphismPreservingParameter M A B l k f ⟶ M :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterInclusion _ _ _

instance fullLevelMorphismPreservingParameterInclusion_closed :
    IsClosedImmersion (fullLevelMorphismPreservingParameterInclusion M A B l k f).left :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterInclusion_closed _ _ _

def FullLevelMorphismPreservingPoint (T : Over S) :=
  {c : T ⟶ M // ∀ (U : Over T.left)
    (z : LocallyConstant U.left (Multiplicative (Fin (2 * g) → ZMod N))),
    ((l.pullback c.left).hom.app (.op U) z).val ≫ (Over.pullback c.left).map f =
      ((k.pullback c.left).hom.app (.op U) z).val}

def fullLevelMorphismPreservingParameterPointEquiv (T : Over S) :
    (T ⟶ fullLevelMorphismPreservingParameter M A B l k f) ≃ FullLevelMorphismPreservingPoint M A B l k f T :=
  (Proper.MorphismEqualityParameters.properMorphismEqualityParameterPointEquiv M (l.schemeIso.hom ≫ A.torsionInclusion N ≫ f)
    (k.schemeIso.hom ≫ B.torsionInclusion N) T).trans
    { toFun c := ⟨c.val, (PullbackPreservationCriterion.fullLevel_pullback_preserves_iff l k f c.val.left).mp c.property⟩
      invFun c := ⟨c.val, (PullbackPreservationCriterion.fullLevel_pullback_preserves_iff l k f c.val.left).mpr c.property⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext rfl }

def fullLevelMorphismPreservingParameterQuasiProjectivePresentation [IsNoetherian S]
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) : Projective.ProjectivePresentations.QuasiProjectivePresentation (fullLevelMorphismPreservingParameter M A B l k f) :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterQuasiProjectivePresentation _ _ _ Q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.MorphismPreservationParameters
