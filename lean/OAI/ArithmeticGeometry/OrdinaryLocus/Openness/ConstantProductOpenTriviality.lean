import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CartesianTrivializationComparison
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantTrivial
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionCoverProjective
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr

/-! # Constant Product Open Triviality -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductOpenTriviality.Construction

noncomputable section

/-! Affine-base cube propagation for constant proper integral factors, using their actual section covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes

variable {K : Type} [Field K] [IsAlgClosed K]
variable {A B X Y S : Scheme} [IsIntegral S] [IsLocallyNoetherian S]
variable [IsIntegral A] [IsIntegral B] [A.IsSeparated] [B.IsSeparated]
variable [X.IsSeparated] [Y.IsSeparated]
variable (a : A ⟶ Spec (.of K)) (b : B ⟶ Spec (.of K)) [IsProper a] [IsProper b]
variable (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] [IsProper g] [Flat f] [Flat g]
variable [GeometricallyIntegral f] [GeometricallyIntegral g]
variable (p : X ⟶ A) (q : Y ⟶ B) (t : S ⟶ Spec (.of K))
variable (hp : IsPullback p f a t) (hq : IsPullback q g b t)
variable (DA : AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data A) (DB : AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data B)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : DA.I) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ (p ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (DA.sectionHom i₀)))
variable (j₀ : DB.I) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ (q ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (DB.sectionHom j₀)))
variable (L : (pullback f g).Modules) (hL : LineBundle.Construction.IsLineBundle L)
variable (eX : (Scheme.Modules.pullback (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).obj L ≅ LineBundle.Construction.structureSheafModule X)
variable (eY : (Scheme.Modules.pullback (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).obj L ≅ LineBundle.Construction.structureSheafModule Y)

include hp hq DA DB hi₀ hj₀ hL eX eY in
omit [X.IsSeparated] [Y.IsSeparated] in
theorem constantProduct_trivial_over_affineOpen (U : S.Opens) (hU : IsAffineOpen U)
    (x : S) (hx : x ∈ U)
    (he : Nonempty ((Scheme.Modules.pullback ((pullback.fst f g ≫ f).fiberι x)).obj L ≅
      LineBundle.Construction.structureSheafModule ((pullback.fst f g ≫ f).fiber x))) :
    Nonempty ((Scheme.Modules.pullback ((pullback.fst f g ≫ f) ⁻¹ᵁ U).ι).obj L ≅
      LineBundle.Construction.structureSheafModule ((pullback.fst f g ≫ f) ⁻¹ᵁ U).toScheme) := by
  classical
  let : LinearOrder DA.I := (Fintype.equivFin DA.I).linearOrder
  let : LinearOrder DB.I := (Fintype.equivFin DB.I).linearOrder
  have : IsAffine U.toScheme := hU
  have : Nonempty U.toScheme := ⟨⟨x, hx⟩⟩
  have : IsIntegral U.toScheme := inferInstance
  have : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  let f' := f ∣_ U
  let g' := g ∣_ U
  let p' := (f ⁻¹ᵁ U).ι ≫ p
  let q' := (g ⁻¹ᵁ U).ι ≫ q
  let t' := U.ι ≫ t
  let hf := (isPullback_morphismRestrict f U).flip
  let hg := (isPullback_morphismRestrict g U).flip
  have hp' : IsPullback p' f' a t' := hf.paste_horiz hp
  have hq' : IsPullback q' g' b t' := hg.paste_horiz hq
  let π := pullback.fst f g ≫ f
  let π' := pullback.fst f' g' ≫ f'
  have : (f ⁻¹ᵁ U).toScheme.IsSeparated := by
    constructor
    rw [← terminal.comp_from f']
    infer_instance
  have : (g ⁻¹ᵁ U).toScheme.IsSeparated := by
    constructor
    rw [← terminal.comp_from g']
    infer_instance
  let m := AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' (f ⁻¹ᵁ U).ι (g ⁻¹ᵁ U).ι U.ι hf hg
  have hm : IsPullback m π' π U.ι :=
    AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' (f ⁻¹ᵁ U).ι (g ⁻¹ᵁ U).ι U.ι hf hg
  have : (pullback f' g').IsSeparated := by
    constructor
    rw [← terminal.comp_from π']
    infer_instance
  have : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty Scheme) :=
    isAffineHom_isStableUnderBaseChange
  have : IsAffineHom t' := inferInstance
  have : IsAffineHom p' := MorphismProperty.of_isPullback hp'.flip ‹IsAffineHom t'›
  have : IsAffineHom q' := MorphismProperty.of_isPullback hq'.flip ‹IsAffineHom t'›
  let P := ((DA.pullback p').product (DB.pullback q') f' g').projectivePresentation π'
  let sX' := AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection f f' (f ⁻¹ᵁ U).ι U.ι hf sX hsX
  let sY' := AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection g g' (g ⁻¹ᵁ U).ι U.ι hg sY hsY
  have hsX' : sX' ≫ f' = 𝟙 _ := AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over f f' (f ⁻¹ᵁ U).ι U.ι hf sX hsX
  have hsY' : sY' ≫ g' = 𝟙 _ := AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over g g' (g ⁻¹ᵁ U).ι U.ι hg sY hsY
  let M := (Scheme.Modules.pullback m).obj L
  let LM : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (pullback f' g') := ⟨M, LineBundle.Construction.isLineBundle_pullback m L hL⟩
  let eX' := (AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)
    m (f ⁻¹ᵁ U).ι (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left f' g' sY' hsY')
    (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left_square f g f' g' (f ⁻¹ᵁ U).ι (g ⁻¹ᵁ U).ι U.ι hf hg sY hsY).symm L).symm ≪≫
      (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).mapIso eX ≪≫ LineBundle.Construction.pullbackStructureSheafIso (f ⁻¹ᵁ U).ι
  let eY' := (AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)
    m (g ⁻¹ᵁ U).ι (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right f' g' sX' hsX')
    (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right_square f g f' g' (f ⁻¹ᵁ U).ι (g ⁻¹ᵁ U).ι U.ι hf hg sX hsX).symm L).symm ≪≫
      (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).mapIso eY ≪≫ LineBundle.Construction.pullbackStructureSheafIso (g ⁻¹ᵁ U).ι
  let VA := fun i ↦ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (DA.sectionHom i)
  let VB := fun j ↦ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (DB.sectionHom j)
  have hcA : iSup VA = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨i, hi⟩ := DA.covers z
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hcB : iSup VB = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨j, hj⟩ := DB.covers z
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
  have hi : ⊤ ≤ sX' ⁻¹ᵁ (p' ⁻¹ᵁ VA i₀) := by
    change ⊤ ≤ (sX' ≫ ((f ⁻¹ᵁ U).ι ≫ p)) ⁻¹ᵁ VA i₀
    rw [← Category.assoc, show sX' ≫ (f ⁻¹ᵁ U).ι = U.ι ≫ sX from hf.lift_fst _ _ _]
    exact fun z _ ↦ hi₀ (show (U.ι z) ∈ (⊤ : S.Opens) from trivial)
  have hj : ⊤ ≤ sY' ⁻¹ᵁ (q' ⁻¹ᵁ VB j₀) := by
    change ⊤ ≤ (sY' ≫ ((g ⁻¹ᵁ U).ι ≫ q)) ⁻¹ᵁ VB j₀
    rw [← Category.assoc, show sY' ≫ (g ⁻¹ᵁ U).ι = U.ι ≫ sY from hg.lift_fst _ _ _]
    exact fun z _ ↦ hj₀ (show (U.ι z) ∈ (⊤ : S.Opens) from trivial)
  let x' : U.toScheme := ⟨x, hx⟩
  let e' := FiberTrivialityBaseChange.Construction.lineBundleFiberTrivialization_baseChange m π π' U.ι hm.w L x' he.some
  obtain ⟨eM⟩ := AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantTrivial.Construction.ProductConstantSeesaw.trivial a b f' g' p' q' t' hp' hq'
    (DA.projectivePresentation a) (DB.projectivePresentation b) P
    VA VB DA.affine DB.affine hcA hcB sX' hsX' sY' hsY' i₀ hi j₀ hj LM eX' eY' x' ⟨e'⟩
  exact ⟨CartesianTrivializationComparison.Construction.cartesianTrivialization_transfer m (π ⁻¹ᵁ U).ι π π' (π ∣_ U) U.ι hm
    (isPullback_morphismRestrict π U).flip L eM⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductOpenTriviality.Construction
