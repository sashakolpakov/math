import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceCondition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ImmersionFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionRepresentation

/-! # Incidence Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceUniversality

noncomputable section

/-! The global closed incidence scheme represents the intrinsic kernel-containment condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M : Over S}
variable (q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : Matrix μ ν Γ(M.left, ⊤))

theorem grassmannIncidence_universal {T : Over S} (x : T ⟶ M) :
    IncidenceCondition.GrassmannIncidenceCondition q k F x ↔
      ∃! g : T ⟶ IncidenceScheme.grassmannIncidenceScheme q k F,
        g ≫ IncidenceScheme.grassmannIncidenceInclusion q k F = x := by
  have h := Closed.ImmersionFactorization.closedImmersion_ideal_factorization (IncidenceScheme.grassmannIncidenceInclusion q k F) x
  rw [IncidenceScheme.grassmannIncidenceInclusion_kernel] at h
  exact (IncidenceCondition.grassmannIncidenceIdeal_vanish_iff q k F x).symm.trans h

def grassmannIncidenceSubfunctor : Subfunctor (yoneda.obj M) where
  obj T := {x | IncidenceCondition.GrassmannIncidenceCondition q k F x}
  map f x hx := by
    apply (IncidenceCondition.grassmannIncidenceIdeal_vanish_iff q k F (f.unop ≫ x)).mp
    have h := (IncidenceCondition.grassmannIncidenceIdeal_vanish_iff q k F x).mpr hx
    change (IncidenceScheme.grassmannIncidenceIdeal q k F).comap (f.unop.left ≫ x.left) = ⊥
    rw [Scheme.IdealSheafData.comap_comp, h, Scheme.IdealSheafData.comap_bot]

def grassmannIncidenceClosedModel : Closed.ConditionIdeals.ClosedConditionModel (grassmannIncidenceSubfunctor q k F) where
  scheme := IncidenceScheme.grassmannIncidenceScheme q k F
  inclusion := IncidenceScheme.grassmannIncidenceInclusion q k F
  closed := IncidenceScheme.grassmannIncidenceInclusion_isClosedImmersion q k F
  factorization _ x := grassmannIncidence_universal q k F x

def grassmannIncidenceRepresentation : yoneda.obj (IncidenceScheme.grassmannIncidenceScheme q k F) ≅
    (grassmannIncidenceSubfunctor q k F).toFunctor :=
  (grassmannIncidenceClosedModel q k F).representation

instance grassmannIncidenceFunctor_isRepresentable :
    (grassmannIncidenceSubfunctor q k F).toFunctor.IsRepresentable :=
  Functor.IsRepresentable.mk' (grassmannIncidenceRepresentation q k F)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceUniversality
