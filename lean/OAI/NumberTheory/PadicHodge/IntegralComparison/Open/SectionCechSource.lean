import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeQuasiIso

/-! # Section Cech Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechSource

noncomputable section

/-! The augmentation of a genuine global-section source cone equals
its source map followed by the canonical open Čech restriction edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A]
  {B : Type a} [Category.{b} B] [Abelian B]
  [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (G : A ⥤ Cᵒᵖ ⥤ B) [G.Additive]
  (r : F ⋙ Functor.const Cᵒᵖ ⟶ G)
  {ι : Type} [Finite ι] (U : ι → C)
  (K : CochainComplex A ℕ) (M : CochainComplex B ℕ)
  (s : M ⟶ (F.mapHomologicalComplex (.up ℕ)).obj K)

local notation "D" => HomologicalComplex.complexOfFunctorsToFunctorToComplex

def cone := ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).map s ≫
  (r.mapHomologicalComplex (.up ℕ)).app K

omit [Finite ι] in
theorem source : s ≫ SectionCechNaturality.edge F G r U K =
    Presheaf.ConeQuasiIso.map U (cone F G r K M s) := by
  exact (GeometricComparison.CechCone.TotalSourceNaturality.CechConeTotalSourceNaturality.augmentation U
    (SectionCechNaturality.diagram G K)
    ((F.mapHomologicalComplex (.up ℕ)).obj K) M
    (SectionCechNaturality.cone F G r K) s).trans
      (congrArg (fun η => GeometricComparison.CechCone.Total.CechConeTotal.augmentation U
        (SectionCechNaturality.diagram G K) M η)
        ((D).map_comp
          (((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).map s)
          ((r.mapHomologicalComplex (.up ℕ)).app K)).symm)

include s in
omit [Finite ι] in
theorem quasiIso (h : QuasiIso (Presheaf.ConeQuasiIso.map U (cone F G r K M s))) :
    QuasiIso (s ≫ SectionCechNaturality.edge F G r U K) :=
  (source F G r U K M s).symm ▸ h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechSource
