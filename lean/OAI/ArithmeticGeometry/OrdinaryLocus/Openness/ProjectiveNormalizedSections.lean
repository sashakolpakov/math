import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectivePolynomialQuotient
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartScalars

/-! # Projective Normalized Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveNormalizedSections.Construction

noncomputable section

/-! Actual homogeneous polynomial sections, normalized on a closed subscheme's affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance projectiveNormalizedSectionsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveTwistUnitSection (j : σ) (n : ℕ) :
    𝟙_ (Proj (homogeneousSubmodule σ R)).Modules ⟶ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n :=
  (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso _).hom ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).symm (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower j n)

instance projectiveTwistUnitSection_chart_isIso (j : σ) (n : ℕ) :
    IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι).map
      (projectiveTwistUnitSection (R := R) j n)) := by
  let s : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n :=
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).symm (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)
  have hs : AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j n)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ s) = 1 := by
    rw [Equiv.apply_symm_apply]
    exact AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self j n
  have : IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j).ι).map s) :=
    TensorUnitCoefficient.Construction.sectionHom_pullback_isIso_of_overCoefficient_one s (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j n) hs
  change IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j).ι).map ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso _).hom ≫ s))
  rw [Functor.map_comp]
  infer_instance

def projectivePolynomialNativeUnitSectionsEquiv (j : σ) (n : ℕ) :
    homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n ≃ₗ[Γ(Spec (.of R), ⊤)]
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        (𝟙_ (Proj (homogeneousSubmodule σ R)).Modules ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) :=
  (AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n).symm.trans
    (((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).mapIso
      (λ_ (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))).toLinearEquiv.symm)

def nativeUnitToPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟙_ Y.Modules ⟶ (Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) :=
  (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).hom ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

def closedProjectiveAmbientPolynomialSectionsMap {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n →ₗ[Γ(Spec (.of R), ⊤)]
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
          AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) :=
  (((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).map
    (nativeUnitToPushforward f ⊗ₘ 𝟙 (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))).hom).comp
      (projectivePolynomialNativeUnitSectionsEquiv j n).toLinearMap

theorem closedProjectiveAmbientPolynomialSectionsMap_eventually_surjective
    [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Function.Surjective (closedProjectiveAmbientPolynomialSectionsMap f j n) := by
  let Y := Proj (homogeneousSubmodule σ R)
  have hunit : LineBundle.Construction.IsLineBundle (𝟙_ Y.Modules) :=
    LineBundle.Construction.isLineBundle_of_iso (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).symm (LineBundle.Construction.isLineBundle_structureSheaf Y)
  have : (𝟙_ Y.Modules).IsQuasicoherent := LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ hunit
  have : (𝟙_ Y.Modules).IsFiniteType := ProjectiveCohomologyFiniteness.Construction.isFiniteType_of_isLineBundle _ hunit
  have : (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (LineBundle.Construction.isLineBundle_structureSheaf X)
  have : ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom _
  let q : 𝟙_ Y.Modules ⟶ (Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) :=
    nativeUnitToPushforward f
  let q₀ : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y ⟶
      (Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Epi q₀ :=
    ClosedImmersionModuleEpi.Construction.closedImmersion_structureModule_epi f
  have : Epi q := by
    change Epi ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).hom ≫ q₀)
    infer_instance
  obtain ⟨b, hb⟩ := AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective
    (M := 𝟙_ Y.Modules) (N := (Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)) q j
  refine ⟨b, fun n hn => ?_⟩
  have hbn := hb n hn
  change Function.Surjective ((q ▷ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n).app ⊤) at hbn
  rw [← tensorHom_id] at hbn
  exact hbn.comp (projectivePolynomialNativeUnitSectionsEquiv j n).surjective

theorem closedProjectiveAmbientPolynomialSectionsMap_coefficient {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ)
    (p : homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n) :
    TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X))
      (projectiveTwistUnitSection (R := R) j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      (closedProjectiveAmbientPolynomialSectionsMap f j n p) =
    ProjectiveChartScalars.Construction.closedProjectiveChartPolynomialAlgHom f j p.val := by
  let P := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let x : Γ(P, ⊤) := (AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n).symm p
  let s := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P).symm (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)
  have : IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j).ι).map
      ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso _).hom ≫ s)) := projectiveTwistUnitSection_chart_isIso j n
  have hs : AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient P (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      (AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j n) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s) = 1 := by
    rw [Equiv.apply_symm_apply]
    exact AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self j n
  change TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient _ (projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    ((nativeUnitToPushforward f ⊗ₘ 𝟙 P).app ⊤ ((λ_ P).inv.app ⊤ x)) = _
  rw [TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient_naturality]
  have hc := TensorUnitCoefficient.Construction.tensorSectionGlobalCoefficient_unit_frame s (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j n) hs x
  change f.app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso _).hom.app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient (𝟙_ _) ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso _).hom ≫ s)
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) ((λ_ P).inv.app ⊤ x))) = _
  rw [hc]
  exact congrArg (f.app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)) (ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap_section_symm j n p).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveNormalizedSections.Construction
