import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion

/-! # Section Bundle Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport

noncomputable section

/-! A sheaf isomorphism transports complete coefficient section bases
and their actual linear-combination maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type v}
variable (c : R →+* Γ(X, ⊤)) {M Q : X.Modules}

theorem coefficientRingSectionAddEquiv_postcomp (f : M ⟶ Q)
    (s : Line.Bundles.structureModule X ⟶ M) :
    RingSectionBasis.coefficientRingSectionAddEquiv c Q (s ≫ f) =
      ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).map f).hom (RingSectionBasis.coefficientRingSectionAddEquiv c M s) := by
  rfl

def coefficientBundleSectionEquiv (e : M ≅ Q) :
    (GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M ≃ₗ[R]
      (GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj Q :=
  ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).mapIso e).toLinearEquiv

theorem coefficientRingBasisFamily_bundleIso (e : M ≅ Q)
    (b : Module.Basis ι R ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M)) (i : ι) :
    RingSectionBasis.coefficientRingBasisFamily c Q (b.map (coefficientBundleSectionEquiv c e)) i =
      RingSectionBasis.coefficientRingBasisFamily c M b i ≫ e.hom := by
  apply (RingSectionBasis.coefficientRingSectionAddEquiv c Q).injective
  rw [coefficientRingSectionAddEquiv_postcomp]
  change RingSectionBasis.coefficientRingSectionAddEquiv c Q
    ((RingSectionBasis.coefficientRingSectionAddEquiv c Q).symm
      (coefficientBundleSectionEquiv c e (b i))) =
    coefficientBundleSectionEquiv c e
      (RingSectionBasis.coefficientRingSectionAddEquiv c M ((RingSectionBasis.coefficientRingSectionAddEquiv c M).symm (b i)))
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem coefficientSectionLinearCombination_postcomp (f : M ⟶ Q)
    (s : ι → (Line.Bundles.structureModule X ⟶ M)) :
    SectionFrameCriterion.coefficientSectionLinearCombination c Q (fun i => s i ≫ f) =
      ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).map f).hom.comp
        (SectionFrameCriterion.coefficientSectionLinearCombination c M s) := by
  have hv : (fun i => RingSectionBasis.coefficientRingSectionAddEquiv c Q (s i ≫ f)) =
      ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).map f).hom ∘
        (fun i => RingSectionBasis.coefficientRingSectionAddEquiv c M (s i)) := by
    funext i
    exact coefficientRingSectionAddEquiv_postcomp c f (s i)
  change Finsupp.linearCombination R _ = _
  rw [hv]
  exact Finsupp.linearCombination_linear_comp R _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport
