import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionDimensionShift

/-! # Resolution Cycle Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionCycleMaps.IntrinsicCech

noncomputable section

/-! Maps of augmented resolutions induce maps of their cycle sequences. The
connecting isomorphism for an acyclic middle term respects these actual maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology
variable {X : TopCat.{u}}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}

/-- The map on the two differentials surrounding a positive degree. -/
def resolutionDifferentialShortComplexMap (ψ : K ⟶ L) (n : ℕ) :
    AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n ⟶ AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex L n where
  τ₁ := ψ.f n
  τ₂ := ψ.f (n + 1)
  τ₃ := ψ.f (n + 2)
  comm₁₂ := ψ.comm n (n + 1)
  comm₂₃ := ψ.comm (n + 1) (n + 2)

def initialResolutionCycleSequenceMap
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (eK : F ⟶ K.X 0) (wK : eK ≫ K.d 0 1 = 0)
    (eL : G ⟶ L.X 0) (wL : eL ≫ L.d 0 1 = 0)
    (f : F ⟶ G) (ψ : K ⟶ L) (h : f ≫ eL = eK ≫ ψ.f 0) :
    AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence K eK wK ⟶ AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence L eL wL where
  τ₁ := f
  τ₂ := ψ.f 0
  τ₃ := ShortComplex.cyclesMap (resolutionDifferentialShortComplexMap ψ 0)
  comm₁₂ := h
  comm₂₃ := (ShortComplex.toCycles_naturality
    (resolutionDifferentialShortComplexMap ψ 0)).symm

def successiveResolutionCycleSequenceMap (ψ : K ⟶ L) (n : ℕ) :
    AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence K n ⟶ AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence L n where
  τ₁ := ShortComplex.cyclesMap (resolutionDifferentialShortComplexMap ψ n)
  τ₂ := ψ.f (n + 1)
  τ₃ := ShortComplex.cyclesMap (resolutionDifferentialShortComplexMap ψ (n + 1))
  comm₁₂ := ShortComplex.cyclesMap_i (resolutionDifferentialShortComplexMap ψ n)
  comm₂₃ := (ShortComplex.toCycles_naturality
    (resolutionDifferentialShortComplexMap ψ (n + 1))).symm

/-- The acyclic-middle isomorphism is the connecting map, so it is natural
for every morphism of the underlying short exact sequences. -/
theorem acyclicMiddleCohomologyShift_naturality
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ)
    (hS₀ : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n))
    (hS₁ : Subsingleton (CategoryTheory.Sheaf.H S.X₂ (n + 1)))
    (hT₀ : Subsingleton (CategoryTheory.Sheaf.H T.X₂ n))
    (hT₁ : Subsingleton (CategoryTheory.Sheaf.H T.X₂ (n + 1)))
    (x : CategoryTheory.Sheaf.H S.X₃ n) :
    AcyclicResolutionDimensionShift.IntrinsicCech.acyclicMiddleCohomologyShift hT n hT₀ hT₁ (CategoryTheory.Sheaf.H.map φ.τ₃ n x) =
      CategoryTheory.Sheaf.H.map φ.τ₁ (n + 1)
        (AcyclicResolutionDimensionShift.IntrinsicCech.acyclicMiddleCohomologyShift hS n hS₀ hS₁ x) := by
  exact HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.δ_naturality n (n + 1) rfl hS hT φ x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionCycleMaps.IntrinsicCech
