import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAmpleNeighborhood
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMPolarizationLine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleSectionEmbedding
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Local Polarization Embedding -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalPolarizationEmbedding

noncomputable section

/-! The original geometric positivity axiom of a polarized abelian
family constructs local closed section embeddings of its canonical line.
No relative-ampleness or projective-presentation input is supplied. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMPolarizationLine.RelativePoincareClasses OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleSectionEmbedding.PolarizationEmbedding

theorem polarizationLine_exists_affine_ample_neighborhood
    {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ IsAffineOpen U ∧
      (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine (A.pullback U.ι).dual (A.pullback U.ι).polarization.isogeny.hom).IsAmple := by
  let K := AlgebraicClosure (S.residueField x)
  let q : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) K)) ≫ S.fromSpecResidueField x
  let f := A.abelian.scheme.hom
  let L := Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom
  obtain ⟨U, hxU, hU, hL⟩ := GeometricAmpleNeighborhood.properFlat_exists_affine_ample_neighborhood_of_geometric_fiber
    f L (pullback.fst f q) (pullback.snd f q) q (IsPullback.of_hasPullback f q)
      (Relative.CMPolarizationLine.RelativePoincareClasses.polarizationLine_fiber_isAmple A q)
  have hx : q (IsLocalRing.closedPoint K) = x :=
    S.fromSpecResidueField_apply x _
  have hp : (L.pullback (pullback.fst f U.ι)).IsAmple :=
    (Cartesian.SectionAmpleness.PolarizationEmbedding.isAmple_pullback_iff_of_cartesian f L (f ⁻¹ᵁ U).ι (f ∣_ U) U.ι
      (isPullback_morphismRestrict f U).flip).mp hL
  obtain ⟨e⟩ := Quotient.exact (Relative.CMPolarizationLine.RelativePoincareClasses.polarizationLine_baseChange_class A.dual
    A.polarization.isogeny.hom U.ι)
  exact ⟨U, hx ▸ hxU, hU, hp.of_iso e.symm⟩

theorem polarized_exists_affine_local_section_embedding
    {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ d : ℕ, 0 < d ∧
        ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.pullback U.ι).abelian.scheme.left,
          AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine (A.pullback U.ι).dual
            (A.pullback U.ι).polarization.isogeny.hom).sheaf d L.sheaf ∧
          ∃ (n : ℕ) (s : Fin (n + 1) →
            (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A.pullback U.ι).abelian.scheme.left ⟶ L.sheaf))
            (hs : ∀ y : (A.pullback U.ι).abelian.scheme.left,
              ∃ i, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)),
            IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism (A.pullback U.ι).abelian.scheme.hom s hs).left := by
  obtain ⟨U, hxU, hU, hL⟩ := polarizationLine_exists_affine_ample_neighborhood A x
  have : IsAffine U.toScheme := hU
  exact ⟨U, hxU, hU, AmpleSectionEmbedding.PolarizationEmbedding.exists_closed_section_embedding _ _ hL⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalPolarizationEmbedding
