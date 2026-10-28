import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Evaluation Object Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.EvaluationObjectIso

noncomputable section

/-! Section quasi-isomorphisms are invariant under an actual site-object isomorphism. -/

open _root_.CategoryTheory Opposite

universe u v r t
variable {C : Type u} [Category.{v} C] (R : Type r) [CommRing R]
  (J : GrothendieckTopology C)

abbrev evaluationFunctor (U : C) := sheafToPresheaf J (ModuleCat.{t} R) ⋙
  (evaluation Cᵒᵖ (ModuleCat.{t} R)).obj (op U)

def iso {U V : C} (e : U ≅ V) : evaluationFunctor R J U ≅ evaluationFunctor R J V :=
  Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{t} R))
    ((evaluation Cᵒᵖ (ModuleCat.{t} R)).mapIso e.symm.op)

theorem quasiIso {U V : C} (e : U ≅ V)
    {K L : CochainComplex (Sheaf J (ModuleCat.{t} R)) ℕ} (f : K ⟶ L)
    [QuasiIso (((evaluationFunctor R J U).mapHomologicalComplex (.up ℕ)).map f)] :
    QuasiIso (((evaluationFunctor R J V).mapHomologicalComplex (.up ℕ)).map f) :=
  QuasiIsoFunctorIso.transport _ _ (NatIso.mapHomologicalComplex (iso R J e) (.up ℕ)) f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.EvaluationObjectIso
