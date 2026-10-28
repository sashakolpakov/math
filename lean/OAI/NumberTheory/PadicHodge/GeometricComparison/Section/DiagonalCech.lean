import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartModuleCechTotal

/-! # Diagonal Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCech.SectionDiagonalCechComparison

noncomputable section

/-! The diagonal of the actual section bifunctor maps to sections of
the original finite Čech total and is a local quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z t
variable (C : Type u) [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (R : Type z) [CommRing R]
  (S : A ⥤ Cᵒᵖ ⥤ ModuleCat.{max z t} R) [S.Additive]
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (h : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  {ι : Type} [Finite ι] (U : ι → C)

local notation "Q" => P ⋙ S.mapHomologicalComplex (ComplexShape.up ℕ)
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source C S P
local notation "η" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.cone C S P h

def map : M ⟶ (S.mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U P) :=
  CechCone.Total.CechConeTotal.augmentation U Q M η ≫ (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S U P).inv

variable (I : C) (i : ι) (hi : I ≤ U i)
abbrev evaluate := (evaluation Cᵒᵖ (ModuleCat.{max z t} R)).obj (op I)
local notation "E" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCech.SectionDiagonalCechComparison.evaluate C R I

include hi in
omit [HasProducts.{0} A] [HasCoproducts.{0} A] in
theorem augmentation_evaluation_quasiIso : QuasiIso
    (((E).mapHomologicalComplex (.up ℕ)).map (CechCone.Total.CechConeTotal.augmentation U Q M η)) := by
  let ηI := CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone E Q M η
  have hrow (V : C) : IsIso ((CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped E Q).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) := h I V
  let hself : QuasiIso (ηI.app (op I)) := by
    dsimp only [ηI]
    rw [CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app, DiagonalCone.SectionDiagonalCone.evaluated_self]
    change QuasiIso (𝟙 (((E).mapHomologicalComplex (.up ℕ)).obj M))
    infer_instance
  have htotal := @Semilattice.SubchartModuleCechTotal.SemilatticeSubchartModuleCechTotal.quasiIso R _ C _ _ U I i hi
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped E Q) hrow
    (((E).mapHomologicalComplex (.up ℕ)).obj M) ηI hself
  have hsquare := CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation E U Q M η
  exact (quasiIso_iff_comp_right _ (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso E U Q).hom).mp
    (hsquare.symm ▸ htotal)

include hi in
theorem evaluation_quasiIso : QuasiIso (((E).mapHomologicalComplex (.up ℕ)).map (SectionDiagonalCechComparison.map C R S P h U)) := by
  have ha := augmentation_evaluation_quasiIso C R S P h U I i hi
  let e := ((E).mapHomologicalComplex (.up ℕ)).mapIso (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S U P)
  have he : QuasiIso e.inv := inferInstance
  rw [SectionDiagonalCechComparison.map]
  erw [CategoryTheory.Functor.map_comp]
  exact (quasiIso_iff_comp_right _ e.inv (hφ' := he)).mpr ha

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCech.SectionDiagonalCechComparison
