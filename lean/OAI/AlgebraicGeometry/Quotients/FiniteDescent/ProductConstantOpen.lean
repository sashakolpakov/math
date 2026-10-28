import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DetectedFrame
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductResidue

/-! # Product Constant Open -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantOpen

noncomputable section

/-! A line bundle on a product of constant projective families, trivial
on the two axes and on one integral fiber, is trivial near that fiber. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ProductConstantFrameNeighborhood

variable {K : Type u} [Field K] {A B X Y S : Scheme.{u}}
variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable [A.IsSeparated] [B.IsSeparated] [X.IsSeparated] [Y.IsSeparated]
variable (a : A ⟶ Spec (.of K)) (b : B ⟶ Spec (.of K))
variable (f : X ⟶ S) (g : Y ⟶ S) [(pullback f g).IsSeparated]
variable [IsProper f] [IsProper g] [Flat f] [Flat g]
variable [GeometricallyIntegral f] [GeometricallyIntegral g]
variable (p : X ⟶ A) (q : Y ⟶ B) (t : S ⟶ Spec (.of K))
variable (hp : IsPullback p f a t) (hq : IsPullback q g b t)
variable (PA : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk a))
variable (PB : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk b))
variable (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (pullback.fst f g ≫ f)))
variable {ι κ : Type u} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → A.Opens) (V : κ → B.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ (p ⁻¹ᵁ U i₀))
variable (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ (q ⁻¹ᵁ V j₀))
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (pullback f g))
variable (eX : (L.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
variable (eY : (L.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)

include hp hq PA PB P hU hV hcU hcV hi₀ hj₀ eX eY

theorem exists_open (x : S) [IsIntegral ((pullback.fst f g ≫ f).fiber x)]
    (he : Nonempty ((L.pullback ((pullback.fst f g ≫ f).fiberι x)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f).fiber x))) :
    ∃ W : S.Opens, x ∈ W ∧ Nonempty
      ((L.pullback ((pullback.fst f g ≫ f) ⁻¹ᵁ W).ι).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f) ⁻¹ᵁ W).toScheme) := by
  classical
  let : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  let : LinearOrder (Σ _ : ι, κ) := (Fintype.equivFin (Σ _ : ι, κ)).linearOrder
  have : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A).IsQuasicoherent := LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A)
  have : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B).IsQuasicoherent := LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial B)
  have : Module.Finite Γ(Spec (.of K), ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex a (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A) U).homology 1) :=
    CechCoverHomology.Construction.CechCoverFiniteness.projective a U hcU hU PA (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A) 1
  have : Module.Finite Γ(Spec (.of K), ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex b (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B) V).homology 1) :=
    CechCoverHomology.Construction.CechCoverFiniteness.projective b V hcV hV PB (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial B) 1
  let D₁ := UniversalCech.Construction.UniversalCechDetector.ofConstantFamily p a f t hp (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A) U
    (fun n i => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU n i.1)
  let D₂ := UniversalCech.Construction.UniversalCechDetector.ofConstantFamily q b g t hq (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B) V
    (fun n i => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection V hV n i.1)
  let U' := fun i => p ⁻¹ᵁ U i
  let V' := fun j => q ⁻¹ᵁ V j
  let e₁ := eX ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).symm
  let e₂ := eY ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).symm
  let r₁ := ProductFamilyCover.Construction.ProductFamilyAxes.left f g U' V' L.sheaf sY hsY j₀ hj₀ ≫
    ((CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor f U').mapIso e₁).hom
  let r₂ := ProductFamilyCover.Construction.ProductFamilyAxes.right f g U' V' L.sheaf sX hsX i₀ hi₀ ≫
    ((CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor g V').mapIso e₂).hom
  have : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    isAffineHom_isStableUnderBaseChange
  have : IsAffineHom t := inferInstance
  have : IsAffineHom p := MorphismProperty.of_isPullback hp.flip ‹IsAffineHom t›
  have : IsAffineHom q := MorphismProperty.of_isPullback hq.flip ‹IsAffineHom t›
  have hU' : ∀ i, IsAffineOpen (U' i) := fun i => (hU i).preimage p
  have hV' : ∀ j, IsAffineOpen (V' j) := fun j => (hV j).preimage q
  have hcU' : iSup U' = ⊤ := ProductCech.Construction.ProductCechCoverProperties.preimage_covers U p hcU
  have hcV' : iSup V' = ⊤ := ProductCech.Construction.ProductCechCoverProperties.preimage_covers V q hcV
  apply DetectedFrame.Construction.DetectedFrameNeighborhood.exists_open (pullback.fst f g ≫ f) P L
    (ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U' V')
    (ProductCech.Construction.ProductCechCoverProperties.covers f g U' V' hcU' hcV')
    (ProductCech.Construction.ProductCechCoverProperties.affine f g U' V' hU' hV') r₁ r₂ D₁ D₂ x he
  exact ProductResidue.Construction.ProductResidueDetector.normalized f g U' V' hU' hV' hcU' hcV'
    sX hsX sY hsY i₀ hi₀ j₀ hj₀ L x he _ _ e₁ e₂

end Construction.ProductConstantFrameNeighborhood

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantOpen
