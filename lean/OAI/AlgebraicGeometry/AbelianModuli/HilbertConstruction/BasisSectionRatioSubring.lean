import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisPullbackSectionSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarSectionGlobalValue

/-! # Basis Section Ratio Subring -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionRatioSubring

noncomputable section

/-! Ratios of a basis generate the ratios of every section once the
structural field scalars are included. All coordinates use actual pullback frames. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators
universe u v
variable {X : Scheme.{u}} {M : X.Modules}

private def ratioFrameCoordinateAddHom {Y : Scheme.{u}} {N : Y.Modules}
    (e : Line.Bundles.structureModule Y ⟶ N) [IsIso e] : (Line.Bundles.structureModule Y ⟶ N) →+ Γ(Y, ⊤) where
  toFun t := Frame.Coordinates.frameCoordinate e t
  map_zero' := by
    change Frame.Coordinates.structureModuleEndValue Y (0 ≫ inv e) = 0
    rw [zero_comp, map_zero]
  map_add' t v := by
    change Frame.Coordinates.structureModuleEndValue Y ((t + v) ≫ inv e) = _
    rw [Preadditive.add_comp, map_add]
    rfl

private def ratioPullbackAddHom (s : Line.Bundles.structureModule X ⟶ M) :
    (Line.Bundles.structureModule X ⟶ M) →+ Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤) :=
  (ratioFrameCoordinateAddHom (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s)).comp
    (BasisPullbackSectionSurjectivity.pullbackSectionAddHom (Ample.LineBundles.sectionNonvanishing s).ι M)

def sectionRatioAddHom (s : Line.Bundles.structureModule X ⟶ M) :
    (Line.Bundles.structureModule X ⟶ M) →+ Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤) where
  toFun := Section.Frames.sectionRatio s
  map_zero' := by
    rw [Frame.Coordinates.sectionRatio_eq_frameCoordinate]
    exact (ratioPullbackAddHom s).map_zero
  map_add' t v := by
    simp only [Frame.Coordinates.sectionRatio_eq_frameCoordinate]
    exact (ratioPullbackAddHom s).map_add t v

theorem sectionRatio_coefficientScalar {K : Type u} [Field K]
    (p : X ⟶ Spec (.of K)) (s t : Line.Bundles.structureModule X ⟶ M) (c : K) :
    Section.Frames.sectionRatio s (Coefficient.ScalarSections.coefficientScalarSection p c t) =
      Coefficient.ModulePresheaf.schemeCoefficientMap ((Ample.LineBundles.sectionNonvanishing s).ι ≫ p) c * Section.Frames.sectionRatio s t := by
  rw [Frame.Coordinates.sectionRatio_eq_frameCoordinate, Frame.Coordinates.sectionRatio_eq_frameCoordinate,
    BasisPullbackSectionSurjectivity.pullbackSection_coefficientScalar]
  let U := Ample.LineBundles.sectionNonvanishing s
  change Frame.Coordinates.structureModuleEndValue U.toScheme
    (Coefficient.ScalarSections.coefficientScalarSection (U.ι ≫ p) c (Ample.LineBundles.pullbackSection U.ι t) ≫ inv (Ample.LineBundles.pullbackSection U.ι s)) = _
  rw [BasisPullbackSectionSurjectivity.coefficientScalarSection_postcomp]
  exact HilbertConstruction.Field.ScalarSectionGlobalValue.coefficientScalarSection_globalValue (U.ι ≫ p) c
    (Ample.LineBundles.pullbackSection U.ι t ≫ inv (Ample.LineBundles.pullbackSection U.ι s))

theorem sectionRatio_mem_of_basis {K : Type u} [Field K]
    (p : X ⟶ Spec (.of K)) (s : Line.Bundles.structureModule X ⟶ M)
    {ι : Type v} [Fintype ι]
    (b : Module.Basis ι K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M))
    (C : Subring Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (hc : ∀ c : K, Coefficient.ModulePresheaf.schemeCoefficientMap ((Ample.LineBundles.sectionNonvanishing s).ι ≫ p) c ∈ C)
    (hb : ∀ i, Section.Frames.sectionRatio s (BasisSectionGeneration.sectionBasisFamily p M b i) ∈ C)
    (t : Line.Bundles.structureModule X ⟶ M) : Section.Frames.sectionRatio s t ∈ C := by
  rw [BasisSectionGeneration.section_eq_basis_linearCombination p M b t]
  change sectionRatioAddHom s (∑ i,
    Coefficient.ScalarSections.coefficientScalarSection p (b.repr (BasisSectionGeneration.coefficientSectionAddEquiv p M t) i)
      (BasisSectionGeneration.sectionBasisFamily p M b i)) ∈ C
  rw [map_sum]
  apply C.sum_mem
  intro i _
  change Section.Frames.sectionRatio s (Coefficient.ScalarSections.coefficientScalarSection p _ (BasisSectionGeneration.sectionBasisFamily p M b i)) ∈ C
  rw [sectionRatio_coefficientScalar]
  exact C.mul_mem (hc _) (hb i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSectionRatioSubring
