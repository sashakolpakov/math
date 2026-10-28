import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation

/-! # Global Functions Finite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.GlobalFunctionsFinite

noncomputable section

/-! The actual global regular-function algebra of a projective scheme is finite over its Noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

local notation "O" => OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X.left

theorem base_value (r : R) : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X ⊤ r =
    X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ ⊤ le_top) r = _
  have ht : X.hom.appLE ⊤ ⊤ le_top = X.hom.appTop := Scheme.Hom.appLE_eq_app X.hom
  rw [ht]
  rfl

def degreeZeroEquiv :
    letI := CoherentFiniteness.coefficientModule R X.hom (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X.left) 0
    AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X.left) 0 ≃ₗ[R]
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op ⊤) := by
  let := AlgebraicGeometry.SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule O 0
  let e := AlgebraicGeometry.SheafCohomology.AffineH.Projective.hZeroCanonicalLinearEquivGlobalSections O
  let := CoherentFiniteness.coefficientModule R X.hom O 0
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro r x
  change e ((X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) • x) =
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X ⊤ r • e x
  rw [base_value]
  exact e.map_smul _ _

theorem finite [IsNoetherianRing R] [IsSeparated X.hom] (hprojective : Projectivity.Construction.ProjectiveOver R X.hom) :
    Module.Finite R ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op ⊤)) := by
  let : (O).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  let : (O).IsFinitePresentation := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_finitePresentation AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  let : (O).IsFiniteType := by
    constructor
    obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData O
    refine ⟨q.localGeneratorsData, ?_⟩
    constructor
    intro i
    exact (hq.isFinite_presentation i).isFiniteType_generators
  let := CoherentFiniteness.coefficientModule R X.hom O 0
  let : Module.Finite R (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H O 0) :=
    CoherentFiniteness.cohomology_finite R X.hom hprojective O 0
  exact Module.Finite.equiv (degreeZeroEquiv R X)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.GlobalFunctionsFinite
