import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GluedCharts
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Global Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: global finite étale representability of actual finite torsors

The actual affine base opens cover the terminal object of the pro-étale
topology. The proved chart bijections therefore make the global comparison
an isomorphism of sheaves. This identifies the glued finite étale scheme
with the original torsor, without a supplied trivialization or descent datum.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The affine base opens cover the terminal object in the actual site. -/
theorem GlobalScheme.Construction.proEtaleDirectedAffine_coversTop (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).CoversTop (GluingData.Construction.proEtaleDirectedAffineDiagram X).obj := by
  intro W
  apply (Scheme.ProEt.topology X).superset_covering _
    (ProEtale.OpenCover.Construction.proEtaleOpenCover_cover W (Affine.BaseCover.Construction.affineBaseCover W))
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T f ⟨i⟩
  exact ⟨i, ⟨Affine.BaseCover.Construction.affineBaseCoverToOpen W i⟩⟩

variable {X : Scheme.{u}} {ℓ n : ℕ} [NeZero (ℓ ^ n)]
  (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- The comparison of the actual torsor sheaf with the glued represented sheaf is an isomorphism. -/
instance App.Construction.FiniteCoefficientExtension.sectionToGluedSheafHom_isIso : IsIso E.sectionToGluedSheafHom := by
  apply Sheaf.isIso_of_coversTop (GlobalScheme.Construction.proEtaleDirectedAffine_coversTop X)
  intro i
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  apply (isIso_iff_bijective _).mpr
  change Function.Bijective (fun s : E.Fiber W.unop.left =>
    (⟨E.sectionToGlued W.unop.left s⟩ : ULift.{u + 1} (W.unop.left ⟶ E.gluedProEt)))
  exact Equiv.ulift.symm.bijective.comp (E.sectionToGlued_bijective_on_chart i W.unop.hom)

/-- The actual global representing isomorphism of presheaves. -/
def App.Construction.FiniteCoefficientExtension.gluedRepresentativeIso : uliftYoneda.{u + 1}.obj E.gluedProEt ≅ E.fiberPresheaf := by
  have : IsIso E.sectionToGluedPresheaf :=
    (ObjectProperty.isIso_hom_iff E.sectionToGluedSheafHom).mpr inferInstance
  exact (asIso E.sectionToGluedPresheaf).symm

/-- The original actual torsor is represented by the glued finite étale scheme. -/
def App.Construction.FiniteCoefficientExtension.gluedRepresentative : E.fiberPresheaf.RepresentableBy E.gluedProEt :=
  (Functor.RepresentableBy.equivUliftYonedaIso E.fiberPresheaf E.gluedProEt).symm
    E.gluedRepresentativeIso

/-- Every actual finite-coefficient torsor on an arbitrary scheme has a finite étale representative. -/
theorem App.Construction.FiniteCoefficientExtension.exists_finiteEtale_representative :
    ∃ T : X.ProEt, IsFinite T.hom ∧ Etale T.hom ∧
      Nonempty (E.fiberPresheaf.RepresentableBy T) :=
  ⟨E.gluedProEt, E.gluedSchemeToBase_finite, E.gluedSchemeToBase_etale,
    ⟨E.gluedRepresentative⟩⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
