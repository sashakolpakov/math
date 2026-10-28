import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.PolarizedDualPointedHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CanonicalDualPoincare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatTensorEpi
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomEpiDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.DualTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.RecoveryComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData

/-! # Canonical Dual Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.CanonicalDualTransport

noncomputable section

/-! A chosen dual covered by the original family can be compared with
any polarized dual on every test scheme. The canonical comparison is a
group isomorphism, proved using the actual covering isogeny. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (T : Over S)
    (D E : Dual.Data.DualAbelianData (A.pullback T.hom))
    (m : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) D.abelian)
    (p : PolarizationData.Polarization E δ) (level : (A.pullback T.hom).FullLevel N)
    (hδ : ∀ i, 0 < δ i)

include P m p level hδ in
/-- The canonical comparison preserves the original group structures;
no polarization or projective presentation of the chosen dual is assumed. -/
theorem canonicalDual_isMonHom_of_coveringIsogeny :
    IsMonHom (D.uniqueUnderlyingIso E).hom := by
  let c := D.uniqueUnderlyingIso E
  let f := m.hom ≫ c.hom
  have hf : η[(A.pullback T.hom).scheme] ≫ f = η[E.abelian.scheme] := by
    change η[(A.pullback T.hom).scheme] ≫ (m.hom ≫ c.hom) = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ c.hom) (IsMonHom.one_hom m.hom)).trans
        (D.uniqueUnderlyingIso_preserves_unit E))
  let : IsMonHom f :=
    Universal.PolarizedDualPointedHomomorphism.universalPolarizedDual_pointedMap_isMonHom A A P P T E p level hδ f hf
  let : Epi (m.hom ⊗ₘ m.hom) := FaithfullyFlatTensorEpi.over_tensor_epi_of_flat_surjective m.hom m.hom
  exact MonoidHomEpiDescent.isMonHom_of_tensor_epi m.hom f c.hom rfl

include P in
/-- The inverse canonical comparison preserves the actual Poincare class. -/
theorem canonicalDual_inverse_poincare_class :
    Line.Bundles.LineBundle.pullbackClass ((D.uniqueUnderlyingIso E).inv ⊗ₘ 𝟙 (A.pullback T.hom).scheme).left
      (Line.Bundles.LineBundle.classOf D.poincare) = Line.Bundles.LineBundle.classOf E.poincare := by
  let c := D.uniqueUnderlyingIso E
  let e : D.abelian.scheme ⊗ (A.pullback T.hom).scheme ≅
      E.abelian.scheme ⊗ (A.pullback T.hom).scheme := c ⊗ᵢ Iso.refl _
  exact Line.Bundles.LineBundle.inverseRecovery e D.poincare E.poincare
    (Universal.CanonicalDualPoincare.universalCanonicalDual_poincare_class A P T D E)

include P m hδ in
/-- Transport a graph-power enhancement to the chosen dual along that
canonical group comparison, retaining its actual graph-power isomorphism. -/
theorem graphPowerEnhancement_on_chosenDual
    (L : Line.Bundles.LineBundle (A.pullback T.hom).scheme.left) (d : ℕ)
    (H : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      (⟨A.pullback T.hom, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N T.left) L d) :
    ∃ q : PolarizationData.Polarization D δ,
      Nonempty (L.sheaf ≅ ((PoincareGraph.Bundles.poincareGraphBundle D q.isogeny.hom).tensorPower d).sheaf) := by
  let c := D.uniqueUnderlyingIso H.dual
  let : IsMonHom c.hom :=
    canonicalDual_isMonHom_of_coveringIsogeny A P T D H.dual m H.polarization level hδ
  let : IsMonHom c.inv := inferInstance
  let e : H.object.dual.abelian.scheme ≅ D.abelian.scheme := c.symm
  let : IsMonHom e.hom := by
    change IsMonHom c.inv
    infer_instance
  have hc : Line.Bundles.LineBundle.pullbackClass (c.inv ⊗ₘ 𝟙 (A.pullback T.hom).scheme).left
      (Line.Bundles.LineBundle.classOf D.poincare) = Line.Bundles.LineBundle.classOf H.dual.poincare :=
    canonicalDual_inverse_poincare_class A P T D H.dual
  let Q := H.object.withDual D e hc
  have hQ : Line.Bundles.LineBundle.classOf Q.graphBundle = Line.Bundles.LineBundle.classOf H.object.graphBundle :=
    H.object.withDual_graphBundle_class D e hc
  let eG : Q.graphBundle.sheaf ≅ H.object.graphBundle.sheaf := (Quotient.exact hQ).some
  exact ⟨Q.polarization,
    ⟨H.powerIso.some ≪≫ (TensorPower.Maps.tensorPowerFunctor _ d).mapIso eG.symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.CanonicalDualTransport
