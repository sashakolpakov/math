import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaExtZeroEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso

/-! # Yoneda Evaluation Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaEvaluationQuasiIso

noncomputable section

/-! Quasi-isomorphisms detected by the original free-source Ext functor
are genuine section quasi-isomorphisms, before any universe lift. -/

open _root_.CategoryTheory Opposite

universe u v z
variable {C : Type (max u v)} [Category.{v} C]
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{max u v} R)] (U : C)

abbrev evaluationFunctor := sheafToPresheaf J (ModuleCat.{max u v} R) ⋙
  (evaluation Cᵒᵖ (ModuleCat.{max u v} R)).obj (op U)

variable [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  {K L : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ} (f : K ⟶ L)

theorem quasiIso
    [QuasiIso (((Ext.ModuleFunctor.functor R
      (Sheaf.freeYoneda J U (ModuleCat.of R R)) 0).mapHomologicalComplex (.up ℕ)).map f)] :
    QuasiIso (((evaluationFunctor R J U).mapHomologicalComplex (.up ℕ)).map f) := by
  have hm := QuasiIsoFunctorIso.transport _ _
    (NatIso.mapHomologicalComplex (YonedaExtZeroEvaluation.iso.{u,v,z} R J U) (.up ℕ)) f
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (((evaluationFunctor R J U).mapHomologicalComplex (.up ℕ)).map f)
    (ModuleCat.uliftFunctor.{z,max u v} R)).mp hm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaEvaluationQuasiIso
