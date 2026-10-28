import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafConeLevelCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismCone
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Regrouped

/-! # Presheaf Global Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafGlobalAugmentation

noncomputable section

/-! Evaluating the actual presheaf-valued Čech total identifies its
global cone augmentation with the global map in the Čech prism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v r t
variable {C : Type u} [SemilatticeInf C]
  (R : Type r) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{t} R) ℕ)
  (P : Cᵒᵖ ⥤ CochainComplex (Cᵒᵖ ⥤ ModuleCat.{t} R) ℕ)
  (a : Q ⋙ (Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ) ⟶ P)

local notation "A" => HomologicalComplex.complexOfFunctorsToFunctorToComplex
local notation "B" => Functor.flip (P ⋙ A)
local notation "T" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.total U P
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.total U Q
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U
local notation "γ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismCone.cone Q P a

abbrev evaluation (V : Cᵒᵖ) := (CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{t} R)).obj V

def coordinates : (A).obj T ≅ B ⋙ G :=
  NatIso.ofComponents (fun V => GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (PresheafGlobalAugmentation.evaluation R V) U P)
    (fun f => GeometricComparison.CechCone.CoefficientTransformation.CechConeCoefficientTransformation.total (PresheafGlobalAugmentation.evaluation R _) (PresheafGlobalAugmentation.evaluation R _)
      ((CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{t} R)).map f) U P)

def level := GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (Functor.const Cᵒᵖ) U Q P a

def cone : (Functor.const Cᵒᵖ).obj M ⟶ (A).obj T :=
  (A).map (level R U Q P a)

theorem cone_coordinates : cone R U Q P a ≫ (coordinates R U P).hom =
    DoubleCechGlobalAugmentation.cone
      (B ⋙ NonemptyCechNerve.complexFunctor U)
      ((NonemptyCechNerve.complexFunctor U).obj Q)
      (CechPrism.GlobalAugmentation.cone U Q B γ) := by
  apply NatTrans.ext
  funext V
  have h := PresheafConeLevelCoordinates.evaluated_level R U Q P a V
  apply h.trans
  change (G).map (PresheafDiagramCone.localMap R Q P a V) =
    𝟙 _ ≫ TripleTotal.RowCoordinates.rowFunctor.map
      (𝟙 _ ≫ (NonemptyCechNerve.complexFunctor U).map ((γ).app V))
  rw [Category.id_comp, Category.id_comp]
  rfl

def map := GeometricComparison.CechCone.Total.CechConeTotal.augmentation U ((A).obj T) M (cone R U Q P a)

theorem map_coordinates : PresheafGlobalAugmentation.map R U Q P a ≫ (G).map (coordinates R U P).hom =
    CechPrism.Regrouped.Comparison.global R U Q B γ := by
  exact (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.augmentation U M (cone R U Q P a)
    (coordinates R U P).hom).trans
      (congrArg (fun c => GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (B ⋙ G) M c)
        (cone_coordinates R U Q P a))

private theorem quasiIso_postcompose {D : Type*} [Category D] [Abelian D]
    {N K L : CochainComplex D ℕ} (b : N ⟶ K) (e : K ≅ L) (c : N ⟶ L)
    (hc : b ≫ e.hom = c) (h : QuasiIso c) : QuasiIso b := by
  apply (quasiIso_iff_comp_right b e.hom).mp
  rw [hc]
  exact h

theorem quasiIso
    (h : QuasiIso (CechPrism.Regrouped.Comparison.global R U Q B γ)) :
    QuasiIso (PresheafGlobalAugmentation.map R U Q P a) :=
  quasiIso_postcompose (PresheafGlobalAugmentation.map R U Q P a) ((G).mapIso (coordinates R U P))
    (CechPrism.Regrouped.Comparison.global R U Q B γ) (map_coordinates R U Q P a) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafGlobalAugmentation
