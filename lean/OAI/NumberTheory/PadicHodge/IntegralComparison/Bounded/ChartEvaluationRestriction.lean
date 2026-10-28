import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartEvaluationCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingChartRestriction

/-! # Chart Evaluation Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartEvaluationRestriction

noncomputable section

/-! Original chart section coordinates intertwine the actual open-presheaf restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} (fZ : Z ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fZ n))
  {U V : Z.Opens} (hVU : V ≤ U)

def map :
    ((BoundedOpen.SectionComplex.evaluation (B := B) U).mapHomologicalComplex (.up ℕ)).obj
      (BoundedOpen.SectionComplex.complex fZ n I) ⟶
    ((BoundedOpen.SectionComplex.evaluation (B := B) V).mapHomologicalComplex (.up ℕ)).obj
      (BoundedOpen.SectionComplex.complex fZ n I) :=
  (HomologicalComplex.asFunctor (BoundedOpen.SectionComplex.complex fZ n I)).map (homOfLE hVU).op

variable (g : X ⟶ Y) (h : Y ⟶ Z) [IsOpenImmersion g] [IsOpenImmersion h]
  (eU : h.opensRange = U) (eV : (g ≫ h).opensRange = V)

theorem component (i : ℕ) :
    (ChartEvaluationCoordinates.iso fZ h n U eU I).hom.f i ≫ (ChartEvaluationRestriction.map fZ n I hVU).f i =
      (IncomingChartRestriction.map fZ g h n I).f i ≫
        (ChartEvaluationCoordinates.iso fZ (g ≫ h) n V eV I).hom.f i := by
  let m := (IncomingChartRestriction.map fZ g h n I).f i
  let a := (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).map
    (ChartEvaluationCoordinates.linearEquiv fZ h n U eU (I.cocomplex.X i)).toModuleIso.hom
  let b := (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).map
    (ChartEvaluationCoordinates.linearEquiv fZ (g ≫ h) n V eV (I.cocomplex.X i)).toModuleIso.hom
  have middle : a ≫ (ChartEvaluationRestriction.map fZ n I hVU).f i = m ≫ b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  exact (congrArg (fun t => t ≫ (ChartEvaluationRestriction.map fZ n I hVU).f i)
    (ChartEvaluationCoordinates.component fZ h n U eU I i)).trans
      (middle.trans (congrArg (fun t => m ≫ t)
        (ChartEvaluationCoordinates.component fZ (g ≫ h) n V eV I i).symm))

theorem complexes :
    (ChartEvaluationCoordinates.iso fZ h n U eU I).hom ≫ ChartEvaluationRestriction.map fZ n I hVU =
      IncomingChartRestriction.map fZ g h n I ≫
        (ChartEvaluationCoordinates.iso fZ (g ≫ h) n V eV I).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component fZ n I hVU g h eU eV i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartEvaluationRestriction
