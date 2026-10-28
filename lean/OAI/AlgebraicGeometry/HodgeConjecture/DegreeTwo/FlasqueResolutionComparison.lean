import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueConeComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExtensionComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ResolutionHomotopy

/-! # Flasque Resolution Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueResolutionComparison.Constructions

noncomputable section

/-! Actual section cohomology of nonnegative flasque resolutions is computed by injective resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}

theorem rationalSheafFlasque_of_isZero (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (hF : IsZero F) :
    TopCat.Sheaf.IsFlasque F where
  epi {U W} i := by
    have : IsIso (F.obj.map i) :=
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U.unop).map_isZero hF).isIso
        ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections W.unop).map_isZero hF) _
    infer_instance

theorem rationalFlasqueComplex_extend
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) c)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (e : c.Embedding c') (i' : ι') :
    TopCat.Sheaf.IsFlasque ((K.extend e).X i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i,hi⟩ := hi'
    have := hK i
    exact ThomGoodShiftFlasque.Constructions.rationalSheafFlasque_of_iso (K.extendXIso e hi).symm
  · exact rationalSheafFlasque_of_isZero _ (K.isZero_extend_X e i' (by simpa using hi'))

theorem rationalFlasqueSections_quasiIso
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (f : K ⟶ L)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) [QuasiIso f] (U : Opens X) :
    QuasiIso (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  have := FlasqueConeComparison.Constructions.rationalBoundedFlasqueSections_quasiIso
    (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
    (rationalFlasqueComplex_extend K hK ComplexShape.embeddingUpNat)
    (rationalFlasqueComplex_extend L hL ComplexShape.embeddingUpNat) 0 U
  exact ExtensionComparison.Constructions.functorQuasiIso_of_extended ComplexShape.embeddingUpNat (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U) f

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (he : ∀ n, K.ExactAt (n+1))
variable (I : InjectiveResolution (K.homology 0))

include hK he

theorem flasqueResolutionLift_sections_quasiIso (U : Opens X) :
    QuasiIso (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ResolutionHomotopy.Constructions.resolutionLift K he I)) := by
  have := ResolutionHomotopy.Constructions.resolutionLift_quasiIso K he I
  exact rationalFlasqueSections_quasiIso (ResolutionHomotopy.Constructions.resolutionLift K he I) hK
    (fun n => FlasqueInjectives.Constructions.injectiveModuleSheaf_isFlasque (I.cocomplex.X n)) U

def flasqueResolutionSectionCohomologyIso (U : Opens X) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K).homology n ≅
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U I.cocomplex).homology n := by
  have := flasqueResolutionLift_sections_quasiIso K hK he I U
  exact isoOfQuasiIsoAt
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ResolutionHomotopy.Constructions.resolutionLift K he I)) n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueResolutionComparison.Constructions
