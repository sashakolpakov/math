import Mathlib.Order.WithBot
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Endpoint Substitution -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.EndpointSubstitution.ProjectiveCech

noncomputable section

/-! Explicit polynomial substitutions for prepending or appending a linear form to a cover. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} {A : Type w}

def prependFamily (a : σ → A) (x : A) : WithBot σ → A := WithBot.recBotCoe x a

def appendFamily (a : σ → A) (x : A) : WithTop σ → A := WithTop.recTopCoe x a

variable (R : Type v) [CommRing R]

def prependLinearSubstitution (l : MvPolynomial σ R) : MvPolynomial (WithBot σ) R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (prependFamily (X (R := R)) l)

def appendLinearSubstitution (l : MvPolynomial σ R) : MvPolynomial (WithTop σ) R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (appendFamily (X (R := R)) l)

theorem prependLinearSubstitution_bot (l : MvPolynomial σ R) : prependLinearSubstitution R l (X ⊥) = l :=
  MvPolynomial.aeval_X _ _

theorem prependLinearSubstitution_coe (l : MvPolynomial σ R) (i : σ) :
    prependLinearSubstitution R l (X (i : WithBot σ)) = X i := MvPolynomial.aeval_X _ _

theorem appendLinearSubstitution_top (l : MvPolynomial σ R) : appendLinearSubstitution R l (X ⊤) = l :=
  MvPolynomial.aeval_X _ _

theorem appendLinearSubstitution_coe (l : MvPolynomial σ R) (i : σ) :
    appendLinearSubstitution R l (X (i : WithTop σ)) = X i := MvPolynomial.aeval_X _ _

variable [CommRing A] [Algebra R A]

theorem aeval_prependFamily (a : σ → A) (l : MvPolynomial σ R) :
    (MvPolynomial.aeval a).comp (prependLinearSubstitution R l) =
      MvPolynomial.aeval (prependFamily a (MvPolynomial.aeval a l)) := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i = ⊥
  · subst i
    rw [AlgHom.comp_apply, prependLinearSubstitution_bot, MvPolynomial.aeval_X]
    rfl
  · obtain ⟨j, rfl⟩ := WithBot.ne_bot_iff_exists.mp hi
    rw [AlgHom.comp_apply, prependLinearSubstitution_coe, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rfl

theorem aeval_appendFamily (a : σ → A) (l : MvPolynomial σ R) :
    (MvPolynomial.aeval a).comp (appendLinearSubstitution R l) =
      MvPolynomial.aeval (appendFamily a (MvPolynomial.aeval a l)) := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i = ⊤
  · subst i
    rw [AlgHom.comp_apply, appendLinearSubstitution_top, MvPolynomial.aeval_X]
    rfl
  · obtain ⟨j, rfl⟩ := WithTop.ne_top_iff_exists.mp hi
    rw [AlgHom.comp_apply, appendLinearSubstitution_coe, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.EndpointSubstitution.ProjectiveCech
