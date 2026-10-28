import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClopenFiniteCoefficientDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeParameterNoetherian
import OAI.ArithmeticGeometry.Models.FoundationsPullback
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Immersion Finite Coefficient Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImmersionFiniteCoefficientDescent

noncomputable section

/-! Closedness of an existing quasi-compact immersion descends to
finite coefficients. The fixed schematic image is formed before base
change; no flatness or reducedness is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.ArithmeticGeometry.Models.FoundationsPullback.Constructions

universe u

private theorem cartesian_range_fst
    {W X Y Z : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback p q f g) : Set.range p = f ⁻¹' Set.range g := by
  have hs : Function.Surjective H.isoPullback.hom := H.isoPullback.hom.homeomorph.surjective
  rw [← H.isoPullback_hom_fst]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hs.range_eq, Set.image_univ, Scheme.Pullback.range_fst]

private theorem openImmersion_pullback_closed_iff
    {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (j : X ⟶ Y) [IsOpenImmersion j.left] :
    IsClosedImmersion ((Over.pullback b).map j).left ↔
      IsClosed (pullback.snd b Y.hom ⁻¹ᵁ j.left.opensRange :
        Set (pullback b Y.hom : Scheme)) := by
  let F := Over.pullback b
  have : IsOpenImmersion (F.map j).left :=
    MorphismProperty.of_isPullback (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback b j).flip
      (inferInstance : IsOpenImmersion j.left)
  have hr : Set.range ((F.map j).left) = pullback.fst Y.hom b ⁻¹' Set.range j.left :=
    cartesian_range_fst (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback b j)
  let e := pullbackSymmetry b Y.hom
  have he : e.hom ≫ pullback.fst Y.hom b = pullback.snd b Y.hom :=
    pullbackSymmetry_hom_comp_fst b Y.hom
  have hopen : e.hom ⁻¹ᵁ (pullback.fst Y.hom b ⁻¹ᵁ j.left.opensRange) =
      pullback.snd b Y.hom ⁻¹ᵁ j.left.opensRange := by
    rw [← Scheme.Hom.comp_preimage, he]
  have hpre : e.hom ⁻¹' Set.range ((F.map j).left) =
      (pullback.snd b Y.hom ⁻¹ᵁ j.left.opensRange : Set (pullback b Y.hom : Scheme)) := by
    rw [hr]
    exact congrArg (fun U : (pullback b Y.hom).Opens =>
      (U : Set (pullback b Y.hom : Scheme))) hopen
  constructor
  · intro h
    have : IsClosedImmersion (F.map j).left := h
    have hc : IsClosed (Set.range ((F.map j).left)) :=
      ((F.map j).left).isClosedEmbedding.isClosed_range
    have hp : IsClosed (e.hom ⁻¹' Set.range ((F.map j).left)) := hc.preimage e.hom.continuous
    exact hpre ▸ hp
  · intro h
    have hp : IsClosed (e.hom ⁻¹' Set.range ((F.map j).left)) := hpre.symm ▸ h
    have hc : IsClosed (Set.range ((F.map j).left)) := e.hom.homeomorph.isClosed_preimage.mp hp
    exact IsClosedImmersion.of_isPreimmersion (F.map j).left hc

theorem closedImmersion_eventually_of_immersion
    (C B : Type) [CommRing C] [CommRing B] [Algebra C B]
    {X Y : Over (Spec (.of C))} [IsNoetherian Y.left]
    (a : X ⟶ Y) [IsImmersion a.left] [QuasiCompact a.left]
    [IsClosedImmersion
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C B)))).map a).left] :
    ∃ s : Finset B,
      IsClosedImmersion ((Over.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B s)).map a).left := by
  let Z : Over (Spec (.of C)) := Over.mk (a.left.imageι ≫ Y.hom)
  let j : X ⟶ Z := Over.homMk a.left.toImage (by
    change a.left.toImage ≫ (a.left.imageι ≫ Y.hom) = X.hom
    rw [← Category.assoc, a.left.toImage_imageι, a.w])
  let k : Z ⟶ Y := Over.homMk a.left.imageι rfl
  have hfac : j ≫ k = a := by
    apply Over.OverMorphism.ext
    exact a.left.toImage_imageι
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion a.left.toImage)
  have : IsClosedImmersion k.left := inferInstanceAs (IsClosedImmersion a.left.imageι)
  have : IsNoetherian Z.left := Finite.TypeParameterNoetherian.finiteType_noetherian_source k.left
  have : QuasiCompact Z.hom := inferInstance
  have : QuasiSeparated Z.hom := inferInstance
  have hU : IsCompact (j.left.opensRange : Set Z.left) := NoetherianSpace.isCompact _
  let b := Spec.map (CommRingCat.ofHom (algebraMap C B))
  let F := Over.pullback b
  have haB : IsClosedImmersion (F.map a).left := inferInstance
  have hkB : IsClosedImmersion (F.map k).left :=
    MorphismProperty.of_isPullback (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback b k).flip
      (inferInstance : IsClosedImmersion k.left)
  have hcomp : (F.map j).left ≫ (F.map k).left = (F.map a).left := by
    change (F.map j ≫ F.map k).left = (F.map a).left
    rw [← F.map_comp, hfac]
  have : IsClosedImmersion ((F.map j).left ≫ (F.map k).left) := by rw [hcomp]; exact haB
  have hjB : IsClosedImmersion (F.map j).left :=
    IsClosedImmersion.of_comp_isClosedImmersion (F.map j).left (F.map k).left
  have hclosed : IsClosed (pullback.snd b Z.hom ⁻¹ᵁ j.left.opensRange :
      Set (pullback b Z.hom : Scheme)) :=
    (openImmersion_pullback_closed_iff b j).mp hjB
  obtain ⟨s, hs⟩ := ClopenFiniteCoefficientDescent.finiteCoefficientOpen_eventually_closed C B Z.hom j.left.opensRange hU hclosed
  let bs := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C B s
  let G := Over.pullback bs
  have hjS : IsClosedImmersion (G.map j).left := (openImmersion_pullback_closed_iff bs j).mpr hs
  have hkS : IsClosedImmersion (G.map k).left :=
    MorphismProperty.of_isPullback (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback bs k).flip
      (inferInstance : IsClosedImmersion k.left)
  have hcompS : (G.map j).left ≫ (G.map k).left = (G.map a).left := by
    change (G.map j ≫ G.map k).left = (G.map a).left
    rw [← G.map_comp, hfac]
  have hc : IsClosedImmersion ((G.map j).left ≫ (G.map k).left) := inferInstance
  refine ⟨s, ?_⟩
  change IsClosedImmersion (G.map a).left
  exact hcompS ▸ hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ImmersionFiniteCoefficientDescent
