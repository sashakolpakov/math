import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSquareComposition
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalNormSections
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenSectionGluing

/-! # Local Norm Refinement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalNormRefinement.Construction

noncomputable section

/-! Local norm sections agree after refinement to any smaller affine
norm chart, independently of its chosen frame and basis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false in
theorem normSquareSection_congr {X Y X' Y' : Scheme.{u}}
    (q : X ⟶ Y) (q' : X' ⟶ Y') (j j' : X' ⟶ X) (i i' : Y' ⟶ Y)
    (h : j ≫ q = q' ≫ i) (h' : j' ≫ q = q' ≫ i') (hj : j = j') (hi : i = i')
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' ≅ (L.pullback i).sheaf)
    (e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' ≅ (L.pullback i').sheaf) (d : ℕ)
    (b : letI := q'.appTop.hom.toAlgebra; Module.Basis (Fin d) Γ(Y', ⊤) Γ(X', ⊤))
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    NormSquareComposition.Construction.normSquareSection q q' j i h L e d z ≫
        (Scheme.Modules.pullbackCongr hi).hom.app (L.tensorPower d).sheaf =
      NormSquareComposition.Construction.normSquareSection q q' j' i' h' L e' d z := by
  subst j'
  subst i'
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app]
  have he : FramedNormSection.Construction.framedNormSection q' e.hom d (SquareSectionComposition.Construction.pullbackSquareSection q q' j i h z) =
      FramedNormSection.Construction.framedNormSection q' e'.hom d (SquareSectionComposition.Construction.pullbackSquareSection q q' j i h z) := by
    exact (congrArg (fun n => FramedNormSection.Construction.framedNormSection q' e.hom n (SquareSectionComposition.Construction.pullbackSquareSection q q' j i h z) =
      FramedNormSection.Construction.framedNormSection q' e'.hom n (SquareSectionComposition.Construction.pullbackSquareSection q q' j i h z)) (Fintype.card_fin d)).mp
        (FramedNormSection.Construction.framedNormSection_frame_independent q' b e.hom e'.hom (SquareSectionComposition.Construction.pullbackSquareSection q q' j i h z))
  exact congrArg (fun a => a ≫ (L.powerBaseChangeIso i d).inv) he

set_option backward.isDefEq.respectTransparency false in
theorem localNormSection_refine {X Y : Scheme.{u}} (q : X ⟶ Y) [IsFinite q]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (d : ℕ) (V U : LocalNormSections.Construction.NormFrameOpen q L d) (h : V.openSet ≤ U.openSet)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    OpenSectionGluing.Construction.refineSectionTo (Y.homOfLE h) U.openSet.ι V.openSet.ι (Y.homOfLE_ι h) (LocalNormSections.Construction.localNormSection U z) =
      LocalNormSections.Construction.localNormSection V z := by
  have : IsAffine U.openSet.toScheme := U.affine
  have : IsAffine V.openSet.toScheme := V.affine
  have : IsAffine (q ⁻¹ᵁ U.openSet).toScheme := isAffine_of_isAffineHom (q ∣_ U.openSet)
  have : IsAffine (q ⁻¹ᵁ V.openSet).toScheme := isAffine_of_isAffineHom (q ∣_ V.openSet)
  let j := X.homOfLE (q.preimage_mono h)
  let i := Y.homOfLE h
  have hj : j ≫ (q ⁻¹ᵁ U.openSet).ι = (q ⁻¹ᵁ V.openSet).ι := X.homOfLE_ι _
  have hi : i ≫ U.openSet.ι = V.openSet.ι := Y.homOfLE_ι h
  have hs : IsPullback j (q ∣_ V.openSet) (q ∣_ U.openSet) i := by
    apply IsPullback.of_right (t := (isPullback_morphismRestrict q U.openSet).flip)
    · simpa only [j, i, Scheme.homOfLE_ι] using (isPullback_morphismRestrict q V.openSet).flip
    · exact (morphismRestrict_homOfLE q V.openSet U.openSet h).symm
  have hc : (j ≫ (q ⁻¹ᵁ U.openSet).ι) ≫ q = (q ∣_ V.openSet) ≫ (i ≫ U.openSet.ι) := by
    rw [hj, hi]
    exact (morphismRestrict_ι q V.openSet).symm
  have hnorm := NormSquareComposition.Construction.normSquareSection_comp q (q ∣_ U.openSet) (q ∣_ V.openSet)
    (q ⁻¹ᵁ U.openSet).ι U.openSet.ι j i (morphismRestrict_ι q U.openSet).symm hs hc
    U.basis L U.frame d z
  exact (congrArg (fun s => s ≫ (Scheme.Modules.pullbackCongr hi).hom.app (L.tensorPower d).sheaf)
    hnorm).trans
    (normSquareSection_congr q (q ∣_ V.openSet) (j ≫ (q ⁻¹ᵁ U.openSet).ι)
      (q ⁻¹ᵁ V.openSet).ι (i ≫ U.openSet.ι) V.openSet.ι hc
      (morphismRestrict_ι q V.openSet).symm hj hi L
      (NormSquareComposition.Construction.compositeNormFrame U.openSet.ι i L U.frame) V.frame d V.basis z)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalNormRefinement.Construction
