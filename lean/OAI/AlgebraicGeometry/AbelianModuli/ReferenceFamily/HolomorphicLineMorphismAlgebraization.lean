import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GeneratedLineMorphismAlgebraization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.HolomorphicMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonGeneratedTwist
import OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections

/-! # Holomorphic Line Morphism Algebraization -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily

/-! Every compatible native holomorphic coefficient family between
arbitrary algebraic line bundles on the original projective variety is
realized by an actual algebraic sheaf morphism. A derived common twist
and faithful tensor transport remove the generating hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier}
    (D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K)

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.exists_algebraic :
    ∃ f : L.sheaf ⟶ K.sheaf, Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V L K f = D := by
  obtain ⟨H, hL, hK⟩ := CommonGeneratedTwist.exists_common_generated_twist V L K
  obtain ⟨n, t, ht⟩ := CommonGeneratedTwist.finiteGlobalGenerators_numbered_sections V (L.tensor H) hL
  obtain ⟨m, s, hs⟩ := CommonGeneratedTwist.finiteGlobalGenerators_numbered_sections V (K.tensor H) hK
  obtain ⟨g, hg⟩ := (D.tensor H).exists_algebraic_of_generated s t hs ht
  obtain ⟨f, hf⟩ := Tensor.LineMorphismEquiv.tensorLineMorphism_surjective L.sheaf K.sheaf H g
  refine ⟨f, ?_⟩
  apply Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensor_injective H
  exact (Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensor_of_algebraic H f).trans
    ((congrArg (Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V (L.tensor H) (K.tensor H)) hf).trans hg)

def Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.algebraicRealization : L.sheaf ⟶ K.sheaf := Classical.choose D.exists_algebraic

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.algebraicRealization_coefficients :
    Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V L K D.algebraicRealization = D :=
  Classical.choose_spec D.exists_algebraic

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.HolomorphicLineMorphismAlgebraization

/-! Native holomorphic coefficients faithfully determine actual algebraic
line-sheaf maps. The algebraization construction is therefore a bijection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lineMorphism_eq_of_coefficients {X : Scheme.{0}} (L K : HilbertConstruction.Line.Bundles.LineBundle X)
    (f g : L.sheaf ⟶ K.sheaf)
    (h : ∀ (r : LineFrameAtlas.LocalLineFrame L.sheaf) (s : LineFrameAtlas.LocalLineFrame K.sheaf)
      (U : X.Opens) (hr : U ≤ r.domain) (hs : U ≤ s.domain),
      LineFrameAtlas.lineMorphismCoefficient f r s U hr hs = LineFrameAtlas.lineMorphismCoefficient g r s U hr hs) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext z
  apply TopCat.Presheaf.section_ext (⟨K.sheaf.presheaf, K.sheaf.isSheaf⟩ :
    TopCat.Sheaf AddCommGrpCat.{0} X) U
  intro x hx
  obtain ⟨r, hr⟩ := LineFrameAtlas.localLineFrames_cover L x
  obtain ⟨s, hs⟩ := LineFrameAtlas.localLineFrames_cover K x
  let W := U ⊓ (r.domain ⊓ s.domain)
  have hW : x ∈ W := ⟨hx, hr, hs⟩
  have hWU : W ≤ U := inf_le_left
  have hWr : W ≤ r.domain := inf_le_right.trans inf_le_left
  have hWs : W ≤ s.domain := inf_le_right.trans inf_le_right
  let w := L.sheaf.presheaf.map (homOfLE hWU).op z
  have he : f.app W w = g.app W w := by
    apply (s.coordinates W hWs).injective
    exact (LineFrameAtlas.rankOneLinearMap_coefficient (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp f W)
      (r.coordinates W hWr) (s.coordinates W hWs) w).trans
      ((congrArg ((r.coordinates W hWr w) * ·) (h r s W hWr hWs)).trans
        (LineFrameAtlas.rankOneLinearMap_coefficient (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp g W)
          (r.coordinates W hWr) (s.coordinates W hWs) w).symm)
  have hf := ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE hWU).op) z
  have hg := ConcreteCategory.congr_hom (g.mapPresheaf.naturality (homOfLE hWU).op) z
  change f.app W w = K.sheaf.presheaf.map (homOfLE hWU).op (f.app U z) at hf
  change g.app W w = K.sheaf.presheaf.map (homOfLE hWU).op (g.app U z) at hg
  have hh := congrArg (K.sheaf.presheaf.germ W x hW) (hf.symm.trans (he.trans hg))
  simpa only [TopCat.Presheaf.germ_res_apply] using hh

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier)

theorem holomorphicLineMorphismCoefficientsOfAlgebraic_injective :
    Function.Injective (Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V L K) := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  intro f g he
  apply lineMorphism_eq_of_coefficients L K f g
  intro r s U hr hs
  apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_ext V.toOver U
  intro x hx
  have hc := congrArg (fun D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K =>
    D.coefficient r s ⟨x, hr hx, hs hx⟩) he
  exact (LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient_value_on_open V f r s U hr hs x hx).symm.trans
    (hc.trans (LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient_value_on_open V g r s U hr hs x hx))

def algebraicHolomorphicLineMorphismEquiv :
    (L.sheaf ⟶ K.sheaf) ≃ Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K :=
  Equiv.ofBijective (Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V L K)
    ⟨holomorphicLineMorphismCoefficientsOfAlgebraic_injective V L K, fun D => D.exists_algebraic⟩

theorem algebraicRealization_of_algebraic (f : L.sheaf ⟶ K.sheaf) :
    (Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V L K f).algebraicRealization = f :=
  holomorphicLineMorphismCoefficientsOfAlgebraic_injective V L K
    (Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.algebraicRealization_coefficients _)

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.HolomorphicLineMorphismAlgebraization

end

end OAI
