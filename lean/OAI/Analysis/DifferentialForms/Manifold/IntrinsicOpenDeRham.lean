import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
import OAI.Analysis.DifferentialForms.Manifold.OpenDeRham
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback

/-! # Intrinsic Open De Rham -/

namespace OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham

noncomputable section

/-!
# De Rham complexes on intrinsic open submanifolds

The actual ambient-local and intrinsic smooth-form presentations determine
isomorphic cochain complexes. Their isomorphism preserves genuine open
restriction and the pullback from the ambient manifold.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

universe u v

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Ambient-local forms and intrinsic open-manifold forms give the same de Rham complex. -/
def intrinsicOpenDeRhamIso (U : Opens M) :
    OpenDeRham.openManifoldDeRhamComplex E U ≅ ManifoldDeRham.manifoldDeRhamComplex E U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).toModuleIso) (by
      intro i j hij
      obtain rfl := (show i + 1 = j from hij)
      rw [OpenDeRham.openManifoldDeRhamComplex_d, ManifoldDeRham.manifoldDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d form)

@[simp]
theorem intrinsicOpenDeRhamIso_hom_f_apply (U : Opens M) (n : ℕ)
    (form : Open.SmoothOpenManifoldForm E U n) :
    (intrinsicOpenDeRhamIso E U).hom.f n form = IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n form := rfl

/-- The cochain isomorphism identifies ambient restriction with intrinsic pullback. -/
theorem intrinsicOpenDeRhamIso_restrict {U V : Opens M} (h : U ≤ V) :
    OpenDeRham.openManifoldDeRhamRestrict E h ≫ (intrinsicOpenDeRhamIso E U).hom =
      (intrinsicOpenDeRhamIso E V).hom ≫ ManifoldDeRhamPullback.manifoldDeRhamPullback (Opens.inclusion h)
        (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict h form

/-- Restricting ambient forms corresponds to pullback along the actual open inclusion. -/
theorem intrinsicOpenDeRhamIso_onOpen (U : Opens M) :
    OpenDeRham.manifoldDeRhamOnOpen E U ≫ (intrinsicOpenDeRhamIso E U).hom =
      ManifoldDeRhamPullback.manifoldDeRhamPullback (Subtype.val : U → M)
        (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen form

/-- The induced identification of the two actual de Rham cohomology presentations. -/
def intrinsicOpenDeRhamCohomologyIso (U : Opens M) (n : ℕ) :
    OpenDeRham.openManifoldDeRhamCohomology E U n ≅ ManifoldDeRham.manifoldDeRhamCohomology E U n :=
  HomologicalComplex.homologyMapIso (intrinsicOpenDeRhamIso E U) n

theorem intrinsicOpenDeRhamCohomologyIso_restrict {U V : Opens M} (h : U ≤ V) (n : ℕ) :
    OpenDeRham.openManifoldDeRhamCohomologyRestrict E h n ≫ (intrinsicOpenDeRhamCohomologyIso E U n).hom =
      (intrinsicOpenDeRhamCohomologyIso E V n).hom ≫
        ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback (Opens.inclusion h)
          (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h) n := by
  change HomologicalComplex.homologyMap (OpenDeRham.openManifoldDeRhamRestrict E h) n ≫
      HomologicalComplex.homologyMap (intrinsicOpenDeRhamIso E U).hom n =
    HomologicalComplex.homologyMap (intrinsicOpenDeRhamIso E V).hom n ≫
      HomologicalComplex.homologyMap
        (ManifoldDeRhamPullback.manifoldDeRhamPullback (Opens.inclusion h)
          (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h)) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    intrinsicOpenDeRhamIso_restrict]

end

end OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham
