import OAI.Analysis.DifferentialForms.Manifold.DeRham
import OAI.Analysis.DifferentialForms.Manifold.Vectors

/-! # De Rham Pullback -/

namespace OAI.Analysis.DifferentialForms.Manifold.DeRhamPullback

noncomputable section

/-!
# De Rham cochain maps induced by actual smooth maps

The degreewise map is the pullback of differential forms along the supplied
smooth map. Its commutation with the differential was proved for that exact
pullback. The induced cohomology maps below therefore retain their geometric
meaning, rather than introducing arbitrary chain maps.
-/

open _root_.CategoryTheory
open scoped ContDiff

universe u
variable {E F G : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- An actual smooth map induces a contravariant map of de Rham complexes. -/
def deRhamPullback (f : E → F) (hf : ContDiff ℝ ∞ f) :
    DeRham.deRhamComplex F ⟶ DeRham.deRhamComplex E :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (Basic.SmoothForm.pullback f hf))
    (fun n => by
      rw [DeRham.deRhamComplex_d, DeRham.deRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact Basic.SmoothForm.d_pullback f hf form)

@[simp] theorem deRhamPullback_f_apply (f : E → F) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (form : Basic.SmoothForm F n) :
    (deRhamPullback f hf).f n form = Basic.SmoothForm.pullback f hf form := rfl

@[simp] theorem deRhamPullback_id :
    deRhamPullback (id : E → E) contDiff_id = 𝟙 (DeRham.deRhamComplex E) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Basic.SmoothForm.pullback_id form

theorem deRhamPullback_comp (f : E → F) (hf : ContDiff ℝ ∞ f)
    (g : F → G) (hg : ContDiff ℝ ∞ g) :
    deRhamPullback (g ∘ f) (hg.comp hf) = deRhamPullback g hg ≫ deRhamPullback f hf := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Basic.SmoothForm.pullback_comp f hf g hg form

/-- Pullback on complex de Rham cohomology induced by a smooth map. -/
def deRhamCohomologyPullback (f : E → F) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    DeRham.deRhamCohomology F n ⟶ DeRham.deRhamCohomology E n :=
  HomologicalComplex.homologyMap (deRhamPullback f hf) n

@[simp] theorem deRhamCohomologyPullback_id (n : ℕ) :
    deRhamCohomologyPullback (id : E → E) contDiff_id n = 𝟙 (DeRham.deRhamCohomology E n) := by
  change HomologicalComplex.homologyMap (deRhamPullback (id : E → E) contDiff_id) n =
    𝟙 ((DeRham.deRhamComplex E).homology n)
  rw [deRhamPullback_id, HomologicalComplex.homologyMap_id]

theorem deRhamCohomologyPullback_comp (f : E → F) (hf : ContDiff ℝ ∞ f)
    (g : F → G) (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    deRhamCohomologyPullback (g ∘ f) (hg.comp hf) n =
      deRhamCohomologyPullback g hg n ≫ deRhamCohomologyPullback f hf n := by
  change HomologicalComplex.homologyMap (deRhamPullback (g ∘ f) (hg.comp hf)) n =
    HomologicalComplex.homologyMap (deRhamPullback g hg) n ≫
      HomologicalComplex.homologyMap (deRhamPullback f hf) n
  rw [deRhamPullback_comp f hf g hg, HomologicalComplex.homologyMap_comp]

/-- Pullback on the actual closed-form subobjects. -/
def deRhamCocyclesPullback (f : E → F) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    DeRham.deRhamCocycles F n ⟶ DeRham.deRhamCocycles E n :=
  HomologicalComplex.cyclesMap (deRhamPullback f hf) n

/-- Pulling back a closed form and then taking its class agrees with pulling
back its de Rham cohomology class. -/
theorem deRhamClass_pullback (f : E → F) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    DeRham.deRhamClass F n ≫ deRhamCohomologyPullback f hf n =
      deRhamCocyclesPullback f hf n ≫ DeRham.deRhamClass E n :=
  HomologicalComplex.homologyπ_naturality (deRhamPullback f hf) n

end

end OAI.Analysis.DifferentialForms.Manifold.DeRhamPullback
