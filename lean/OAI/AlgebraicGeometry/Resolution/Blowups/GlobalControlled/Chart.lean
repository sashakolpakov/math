import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Ideal
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafIdentification
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianCoordinateTransform

/-! # Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Chart.Construction

noncomputable section

/-! The global controlled ideal restricts to the exact controlled ideals on actual Rees charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

private theorem exists_refined_cover_point {Y : Scheme.{u}} (C : Y.OpenCover)
    (D : ∀ i : C.I₀, (C.X i).OpenCover) (x : Y) :
    ∃ p : Σ i : C.I₀, (D i).I₀, x ∈ Set.range ((D p.1).f p.2 ≫ C.f p.1) := by
  obtain ⟨i, y, hy⟩ := C.exists_eq x
  obtain ⟨j, z, hz⟩ := (D i).exists_eq y
  exact ⟨⟨i, j⟩, z, (congrArg (C.f i) hz).trans hy⟩

section Affine

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The quotient of the total affine kernel ideals by the center power is
the kernel ideal of the actual controlled transform. -/
theorem affine_controlled_kernel_identity (I J : Ideal R) (b : ℕ) (a : I) :
    letI : IsNoetherianRing (Blowup.Charts.Construction.blowupChart I a) := NoetherianCoordinateTransform.Construction.blowupChart_isNoetherian I a
    NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (Blowups.Affine.QuotientKernel.Construction.affineQuotientKernel (J.map (Blowup.Charts.Construction.blowupChartConstants I a)))
      ((Blowups.Affine.QuotientKernel.Construction.affineQuotientKernel (I.map (Blowup.Charts.Construction.blowupChartConstants I a))) ^ b) =
        Blowups.Affine.QuotientKernel.Construction.affineQuotientKernel (ControlledTransform.Construction.blowupControlledTransform I J b a) := by
  let : IsNoetherianRing (Blowup.Charts.Construction.blowupChart I a) := NoetherianCoordinateTransform.Construction.blowupChart_isNoetherian I a
  rw [← Blowups.Affine.QuotientKernel.Construction.affineQuotientKernel_pow, Blowups.Affine.QuotientKernel.Construction.affineQuotientKernel_colon]
  congr 1
  rw [ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.span_singleton_pow]
  rfl

end Affine

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The actual denominator chart in the global blowup. -/
def globalBlowupReesChart (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) (a : I.ideal U) :
    Spec (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) a)) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI :=
  Proj.awayι (ReesGrading.Construction.reesGrade (I.ideal U)) (Blowup.Charts.Construction.reesGenerator (I.ideal U) a)
    (Blowup.Charts.Construction.reesGenerator_mem (I.ideal U) a) (by decide) ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI U

instance globalBlowupReesChart_isOpenImmersion (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) (a : I.ideal U) : IsOpenImmersion (globalBlowupReesChart I hI U a) := by
  dsimp only [globalBlowupReesChart]
  infer_instance

theorem globalBlowupReesChart_over (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) (a : I.ideal U) :
    globalBlowupReesChart I hI U a ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI =
      Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants (I.ideal U) a)) ≫ U.2.fromSpec := by
  rw [globalBlowupReesChart, Category.assoc, GlobalBlowup.Data.Construction.globalBlowupChart_over,
    ← Category.assoc, Blowup.Charts.Construction.affineBlowup_chart_structureMap]

/-- Every point of the global blowup lies in one of the actual denominator charts. -/
theorem exists_globalBlowupReesChart (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (x : GlobalBlowup.Data.Construction.globalBlowup I hI) :
    ∃ p : Σ U : X.affineOpens, I.ideal U, x ∈ Set.range (globalBlowupReesChart I hI p.1 p.2) := by
  exact exists_refined_cover_point (GlobalBlowup.Data.Construction.blowupGluingData I hI).cover
    (fun U => (Blowup.Cover.Construction.affineBlowupAffineCover (I.ideal U)).openCover) x

/-- A native affine open cover of the global blowup by the explicit Rees charts. -/
def globalBlowupReesAffineCover (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    (GlobalBlowup.Data.Construction.globalBlowup I hI).AffineOpenCover where
  I₀ := Σ U : X.affineOpens, I.ideal U
  X p := .of (Blowup.Charts.Construction.blowupChart (I.ideal p.1) p.2)
  f p := globalBlowupReesChart I hI p.1 p.2
  idx x := (exists_globalBlowupReesChart I hI x).choose
  covers x := (exists_globalBlowupReesChart I hI x).choose_spec

/-- The native global controlled ideal agrees exactly with the previously
proved algebraic controlled ideal on every actual denominator chart. -/
theorem globalBlowupControlledIdeal_comap_reesChart (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (b : ℕ) (U : X.affineOpens) (a : I.ideal U) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (globalBlowupReesChart I hI U a) =
      Blowups.Affine.QuotientKernel.Construction.affineQuotientKernel (ControlledTransform.Construction.blowupControlledTransform (I.ideal U) (J.ideal U) b a) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing (Blowup.Charts.Construction.blowupChart (I.ideal U) a) := NoetherianCoordinateTransform.Construction.blowupChart_isNoetherian (I.ideal U) a
  rw [GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal, GlobalControlled.Ideal.Construction.controlledIdealSheaf_comap_open]
  unfold GlobalControlled.Ideal.Construction.controlledIdealSheaf
  rw [globalBlowupReesChart_over, Blowups.Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel,
    Blowups.Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel]
  exact affine_controlled_kernel_identity (I.ideal U) (J.ideal U) b a

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Chart.Construction
