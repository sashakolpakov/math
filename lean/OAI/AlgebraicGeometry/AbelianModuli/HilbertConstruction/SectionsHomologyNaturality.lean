import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionCycleMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecifiedCyclesNaturality

/-! # Sections Homology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsHomologyNaturality.IntrinsicCech

noncomputable section

/-! Naturality of the description of positive section homology as a cycle cokernel. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{u}}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}

def sheafTopSectionsMap (ψ : K ⟶ L) : AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex K ⟶ AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex L :=
  ((AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X).mapHomologicalComplex (.up ℕ)).map ψ

def sectionsCycleCokernelMap (ψ : K ⟶ L) (n : ℕ) :
    cokernel ((AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).toCycles.hom.app (op ⊤)) ⟶
      cokernel ((AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex L n).toCycles.hom.app (op ⊤)) :=
  cokernel.map _ _ ((ψ.f n).hom.app (op ⊤))
    ((ShortComplex.cyclesMap (ResolutionCycleMaps.IntrinsicCech.resolutionDifferentialShortComplexMap ψ n)).hom.app (op ⊤))
    (congrArg (fun k => k.hom.app (op ⊤))
      (ShortComplex.toCycles_naturality (ResolutionCycleMaps.IntrinsicCech.resolutionDifferentialShortComplexMap ψ n)))

private theorem sectionHomologyIsoSc_naturality
    {C D : CochainComplex AddCommGrpCat.{u} ℕ} (f : C ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap f (n + 1) ≫
        (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom =
      (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u} (.up ℕ)
            n (n + 1) (n + 2)).map f) := by
  exact (Functor.isoWhiskerRight
    (HomologicalComplex.natIsoSc' AddCommGrpCat.{u} (.up ℕ)
      n (n + 1) (n + 2) (by simp) (by simp))
    (ShortComplex.homologyFunctor AddCommGrpCat.{u})).hom.naturality f

theorem sheafTopSectionsHomologyCokernelIso_naturality (ψ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (sheafTopSectionsMap ψ) (n + 1) ≫
        (AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsHomologyCokernelIso L n).hom =
      (AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsHomologyCokernelIso K n).hom ≫ sectionsCycleCokernelMap ψ n := by
  let S := AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n
  let T := AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex L n
  let E := AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation X
  let φ := ResolutionCycleMaps.IntrinsicCech.resolutionDifferentialShortComplexMap ψ n
  have wi : E.map S.iCycles ≫ (S.map E).g = 0 := by
    erw [← E.map_comp, S.iCycles_g, E.map_zero]
  have wj : E.map T.iCycles ≫ (T.map E).g = 0 := by
    erw [← E.map_comp, T.iCycles_g, E.map_zero]
  have hi : IsLimit (KernelFork.ofι (E.map S.iCycles) wi) :=
    KernelFork.mapIsLimit _ S.cyclesIsKernel E
  have hj : IsLimit (KernelFork.ofι (E.map T.iCycles) wj) :=
    KernelFork.mapIsLimit _ T.cyclesIsKernel E
  have ha : E.map S.toCycles ≫ E.map S.iCycles = (S.map E).f := by
    rw [← E.map_comp, S.toCycles_i]
    rfl
  have hb : E.map T.toCycles ≫ E.map T.iCycles = (T.map E).f := by
    rw [← E.map_comp, T.toCycles_i]
    rfl
  have hz : E.map (ShortComplex.cyclesMap φ) ≫ E.map T.iCycles =
      E.map S.iCycles ≫ (E.mapShortComplex.map φ).τ₂ := by
    change E.map (ShortComplex.cyclesMap φ) ≫ E.map T.iCycles =
      E.map S.iCycles ≫ E.map φ.τ₂
    rw [← E.map_comp, ← E.map_comp, ShortComplex.cyclesMap_i]
  have hab : E.map S.toCycles ≫ E.map (ShortComplex.cyclesMap φ) =
      (E.mapShortComplex.map φ).τ₁ ≫ E.map T.toCycles := by
    change E.map S.toCycles ≫ E.map (ShortComplex.cyclesMap φ) =
      E.map φ.τ₁ ≫ E.map T.toCycles
    rw [← E.map_comp, ← E.map_comp, ShortComplex.toCycles_naturality]
  have hc := SpecifiedCyclesNaturality.homologySpecifiedCyclesIso_naturality (E.mapShortComplex.map φ)
    (E.map S.iCycles) wi hi (E.map S.toCycles) ha
    (E.map T.iCycles) wj hj (E.map T.toCycles) hb
    (E.map (ShortComplex.cyclesMap φ)) hz hab
  simp only [AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsHomologyCokernelIso, Iso.trans_hom]
  rw [← Category.assoc, sectionHomologyIsoSc_naturality, Category.assoc]
  convert congrArg (fun k =>
    ((AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex K).homologyIsoSc' n (n + 1) (n + 2)
      (by simp) (by simp)).hom ≫ k) hc using 1 <;> simp only [Category.assoc] <;> congr 2 <;> first | rfl | (congr 2; first | rfl | exact Subsingleton.elim _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsHomologyNaturality.IntrinsicCech
