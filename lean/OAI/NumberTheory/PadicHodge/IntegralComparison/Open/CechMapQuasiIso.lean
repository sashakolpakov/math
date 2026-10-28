import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechNaturality

/-! # Cech Map Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CechMapQuasiIso.Section

noncomputable section

/-! Changing the source of an actual open Čech comparison by an
isomorphism preserves its quasi-isomorphism property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A]
  {B : Type a} [Category.{b} B] [Abelian B]
  [HasProducts.{0} B] [HasCoproducts.{0} B]
  (G : A ⥤ Cᵒᵖ ⥤ B) [G.Additive]
  {ι : Type} [Finite ι] (U : ι → C)

local notation "D" => HomologicalComplex.complexOfFunctorsToFunctorToComplex

def functor := G.mapHomologicalComplex (.up ℕ) ⋙ D ⋙ GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U

variable {K L I : CochainComplex A ℕ} (e : K ≅ L) (f : K ⟶ I)
  (hf : QuasiIso (SectionCechNaturality.map G U f))

include hf in
omit [HasCoproducts B] [Finite ι] in
theorem quasiIso : QuasiIso (SectionCechNaturality.map G U (e.inv ≫ f)) := by
  change QuasiIso ((functor G U).map (e.inv ≫ f))
  rw [Functor.map_comp]
  exact quasiIso_comp ((functor G U).map e.inv) ((functor G U).map f) (hφ' := hf)

omit hf in
omit [HasCoproducts B] [Finite ι] in
theorem quasiIso_of_map
    (h : QuasiIso ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
      ((D).map ((G.mapHomologicalComplex (.up ℕ)).map f)))) :
    QuasiIso (SectionCechNaturality.map G U (e.inv ≫ f)) :=
  quasiIso G U e f h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CechMapQuasiIso.Section
