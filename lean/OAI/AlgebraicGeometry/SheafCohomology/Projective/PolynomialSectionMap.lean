import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionMapDefs
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitSection
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartScalars

/-! # Polynomial Section Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionMap

noncomputable section

/-! Eventual surjectivity of actual homogeneous polynomial sections onto a projective closed subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Dimension

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient.Construction

universe u

local instance projectivePolynomialSectionMapMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem closedProjectiveAmbientPolynomialSectionsMap_eventually_surjective
    [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Function.Surjective (PolynomialSectionMapDefs.Dimension.closedProjectiveAmbientPolynomialSectionsMap f j n) := by
  let Y := Proj (homogeneousSubmodule σ R)
  have hunit : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle (𝟙_ Y.Modules) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_of_iso (TensorSections.monoidalUnitObjIso Y).symm (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf Y)
  have : (𝟙_ Y.Modules).IsQuasicoherent := ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ hunit
  have : (𝟙_ Y.Modules).IsFiniteType := PolynomialQuotient.Dimension.isFiniteType_of_isLineBundle _ hunit
  have : (Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf X)
  have : ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X)).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom _
  let q : 𝟙_ Y.Modules ⟶ (Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) :=
    PolynomialSectionMapDefs.Dimension.nativeUnitToPushforward f
  let q₀ : Invertible.Scheme.Modules.unitObj Y ⟶
      (Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Epi q₀ :=
    ArithmeticGeometry.OrdinaryLocus.Openness.ClosedImmersionModuleEpi.Construction.closedImmersion_structureModule_epi f
  have : Epi q := by
    change Epi ((TensorSections.monoidalUnitObjIso Y).hom ≫ q₀)
    infer_instance
  obtain ⟨b, hb⟩ := GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective
    (M := 𝟙_ Y.Modules) (N := (Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X)) q j
  refine ⟨b, fun n hn => ?_⟩
  have hbn := hb n hn
  change Function.Surjective ((q ▷ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n).app ⊤) at hbn
  rw [← tensorHom_id] at hbn
  exact hbn.comp (PolynomialSectionMapDefs.Dimension.projectivePolynomialNativeUnitSectionsEquiv j n).surjective

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionMap
