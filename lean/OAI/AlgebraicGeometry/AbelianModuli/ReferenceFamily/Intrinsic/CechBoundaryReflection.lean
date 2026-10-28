import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.CechPotentialAdd

/-! # Cech Boundary Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechBoundaryReflection

noncomputable section

/-! A zero class of the evaluated algebraic cocycle in actual native
holomorphic sheaf cohomology gives an algebraic Cech coboundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)
    (hU : iSup U = ⊤) (z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤))
    (hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0)

def nativeCechOneClass : CategoryTheory.Sheaf.H
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace) 1 :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of V.analyticSpace) (CechDifferential.nativeCechCover V U)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace) (CechDifferential.nativeCechCover_covers V U hU)
    0 (CechDifferential.nativeCechCochain V U 1 z) (CechDifferential.nativeCechCochain_closed V U 1 z hz)

theorem holomorphicCechPrimitive_of_nativeClass_zero
    (hzero : nativeCechOneClass V U hU z hz =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of V.analyticSpace)) 1).obj
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace))) :
    Nonempty (Holomorphic.CechPotentialMem.HolomorphicCechPrimitive V U z) := by
  let F := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace
  obtain ⟨b, hb⟩ := Cech.Add.cech_one_boundary_of_sheaf_class_zero (X := TopCat.of V.analyticSpace)
    (CechDifferential.nativeCechCover V U) F (CechDifferential.nativeCechCover_covers V U hU) (CechDifferential.nativeCechCochain V U 1 z)
    (CechDifferential.nativeCechCochain_closed V U 1 z hz) hzero
  obtain ⟨s, hs⟩ := Cech.Add.cech_zero_eq_localSections (X := TopCat.of V.analyticSpace) (CechDifferential.nativeCechCover V U) F b
  let t (i : I) : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := CechDifferential.nativeCechCover V U i) := s i
  have hi (i : I) : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation
      (Cech.ExtensionCoordinates.cechIntersection U 0 (Cech.PairCoordinates.cechSingletonIndex i)) ≤ CechDifferential.nativeCechCover V U i := by
    intro x hx
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U i
    rwa [Cech.PairCoordinates.cechIntersection_singleton] at hx
  refine ⟨{
    coefficient := fun i => DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (hi i) (t i)
    difference := ?_ }⟩
  intro i j x hix hjx
  have hx : x ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechDifferential.nativeCechCover V U) (Cech.PairCoordinates.cechPairIndex i j) :=
    (CechDifferential.nativeCechIntersection_mem V U 1 (Cech.PairCoordinates.cechPairIndex i j) x).mpr (Holomorphic.CechPotentialMem.cechPair_mem U i j _ hix hjx)
  have hd := congrFun hb (Cech.PairCoordinates.cechPairIndex i j)
  rw [← hs, DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta] at hd
  have hv := congrArg (fun f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechDifferential.nativeCechCover V U) (Cech.PairCoordinates.cechPairIndex i j)) =>
        f ⟨x, hx⟩) hd
  change t j ⟨x, _⟩ - t i ⟨x, _⟩ = CechDifferential.nativeCechFunction V U 1 z (Cech.PairCoordinates.cechPairIndex i j) ⟨x, hx⟩ at hv
  rw [CechDifferential.nativeCechCochain_value] at hv
  exact hv.symm

theorem algebraicCech_boundary_of_nativeClass_zero
    (hzero : nativeCechOneClass V U hU z hz =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of V.analyticSpace)) 1).obj
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace))) :
    ∃ b : Γ(Cech.TermModules.cechTermModule V.carrier U 0, ⊤), (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 0).app ⊤ b = z := by
  obtain ⟨D⟩ := holomorphicCechPrimitive_of_nativeClass_zero V U hU z hz hzero
  exact D.exists_algebraic_boundary hU hz

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechBoundaryReflection
