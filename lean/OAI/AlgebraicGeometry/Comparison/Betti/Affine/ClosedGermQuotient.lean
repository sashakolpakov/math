import OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicRetract
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermMap
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Closed Germ Quotient -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedGermQuotient.AnalyticLocal

noncomputable section

section

/-! A genuine affine closed immersion pulls holomorphic germs back surjectively, compatibly with regular functions. -/

open Set Filter
open scoped _root_.Topology ContDiff

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] {n m : ℕ}
    (h : A →ₐ[ℂ] B)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source)

def affineChartGermPullback : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (f (x.comp h)) →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) :=
  LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt (fun z => f ((e.symm z).comp h)) (e x)
    (ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx) (f (x.comp h))
    (by rw [e.left_inv hx])

theorem affineChartGermPullback_regular :
    (affineChartGermPullback h e f he hf x hx hfx).comp (ChartGermMap.AnalyticLocal.affineChartGermMap f hf (x.comp h) hfx) =
      (ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx).comp h.toRingHom := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change (LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt (fun z => f ((e.symm z).comp h)) (e x)
    (ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx) (f (x.comp h))
    (by rw [e.left_inv hx]) (ChartGermMap.AnalyticLocal.affineChartGermMap f hf (x.comp h) hfx a)).val =
      (ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx (h a)).val
  erw [LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt_val, ChartGermMap.AnalyticLocal.affineChartGermMap_val, ChartGermMap.AnalyticLocal.affineChartGermMap_val]
  apply Germ.coe_eq.mpr
  filter_upwards [ComplexPoints.Analytic.SmoothClosedImmersion.affineChartComap_neighborhood h e f x hx hfx] with z hz
  change f.symm (f ((e.symm z).comp h)) a = e.symm z (h a)
  rw [f.left_inv hz.2]
  rfl

theorem affineChartGermPullback_surjective (hh : Function.Surjective h) :
    Function.Surjective (affineChartGermPullback h e f he hf x hx hfx) := by
  obtain ⟨g, hg, hgf⟩ := ComplexPoints.Analytic.SmoothClosedImmersion.exists_affineChartComap_localLeftInverse h hh e f he hf x hx hfx
  exact LocalHolomorphicRetract.Analytic.localHolomorphicCompositionAt_surjective_of_leftInverse
    (fun z => f ((e.symm z).comp h)) (e x)
    (ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx) (f (x.comp h))
    (by rw [e.left_inv hx]) g hg hgf

end

/-! The actual closed-immersion germ map factors through the analytically extended algebraic ideal. -/

open Set Filter
open scoped _root_.Topology ContDiff

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] {n m : ℕ}
    (h : A →ₐ[ℂ] B)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source)

def affineClosedGermIdeal : Ideal (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (f (x.comp h))) :=
  Ideal.map (ChartGermMap.AnalyticLocal.affineChartGermMap f hf (x.comp h) hfx) (RingHom.ker h.toRingHom)

theorem affineClosedGermIdeal_le_ker :
    affineClosedGermIdeal h f hf x hfx ≤ RingHom.ker (affineChartGermPullback h e f he hf x hx hfx) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change affineChartGermPullback h e f he hf x hx hfx (ChartGermMap.AnalyticLocal.affineChartGermMap f hf (x.comp h) hfx a) = 0
  have hs := RingHom.congr_fun (affineChartGermPullback_regular h e f he hf x hx hfx) a
  change affineChartGermPullback h e f he hf x hx hfx (ChartGermMap.AnalyticLocal.affineChartGermMap f hf (x.comp h) hfx a) =
    ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx (h a) at hs
  exact hs.trans ((congrArg (ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx) ha).trans (map_zero _))

def affineClosedGermQuotientMap :
    (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (f (x.comp h)) ⧸ affineClosedGermIdeal h f hf x hfx) →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) :=
  Ideal.Quotient.lift _ (affineChartGermPullback h e f he hf x hx hfx)
    (affineClosedGermIdeal_le_ker h e f he hf x hx hfx)

theorem affineClosedGermQuotientMap_regular (a : A) :
    affineClosedGermQuotientMap h e f he hf x hx hfx
      (Ideal.Quotient.mk _ (ChartGermMap.AnalyticLocal.affineChartGermMap f hf (x.comp h) hfx a)) =
        ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx (h a) :=
  RingHom.congr_fun (affineChartGermPullback_regular h e f he hf x hx hfx) a

theorem affineClosedGermQuotientMap_surjective (hh : Function.Surjective h) :
    Function.Surjective (affineClosedGermQuotientMap h e f he hf x hx hfx) := by
  intro b
  obtain ⟨a, ha⟩ := affineChartGermPullback_surjective h e f he hf x hx hfx hh b
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedGermQuotient.AnalyticLocal
