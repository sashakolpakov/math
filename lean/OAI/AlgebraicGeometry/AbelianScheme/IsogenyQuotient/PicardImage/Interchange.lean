import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameterFactors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupInterchange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberInterchangePullback

/-! # Interchange -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Interchange.Construction

noncomputable section

/-! The image horizontal and vertical products satisfy interchange on
every test scheme, by universal parameter pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

variable [IsCommMonObj C] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

attribute [local instance] InterchangeParameter.Construction.lineInterchangeParameter_smooth InterchangeParameter.Construction.lineInterchangeParameter_proper InterchangeParameter.Construction.lineInterchangeParameter_connected
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageProducts_interchange {T : Over (Spec (.of k))}
    (c a b x ca cb ax bx w : T ⟶ C ⊗ B)
    (hax : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a x ax)
    (hbx : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) b x bx)
    (hcb : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) c b cb)
    (hca : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) c a ca)
    (hby : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) cb ax w)
    (haz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) ca bx w)
    (U : T.left.Opens) (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) c, U))
    (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) a, U)) (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) b, U))
    (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac cb ax w hby).app U ((GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac c b cb hcb).app U sc sb)
      ((GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a x ax hax).app U sa sx) =
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac ca bx w haz).app U ((GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac c a ca hca).app U sc sa)
      ((GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac b x bx hbx).app U sb sx) := by
  let c₀ := InterchangeParameters.Construction.lineInterchangePointC C B
  let a₀ := InterchangeParameters.Construction.lineInterchangePointA C B
  let b₀ := InterchangeParameters.Construction.lineInterchangePointB C B
  let x₀ := InterchangeParameters.Construction.lineInterchangePointX C B
  let ca₀ := InterchangeParameters.Construction.lineInterchangePointCA C B
  let cb₀ := InterchangeParameters.Construction.lineInterchangePointCB C B
  let ax₀ := InterchangeParameters.Construction.lineInterchangePointAX C B
  let bx₀ := InterchangeParameters.Construction.lineInterchangePointBX C B
  let w₀ := InterchangeParameters.Construction.lineInterchangePointW C B
  let r := InterchangeParameterFactors.Construction.lineInterchangeParameterLift c a b
  have hc : r ≫ c₀ = c := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointC c a b
  have ha : r ≫ a₀ = a := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointA c a b hca.2.1
  have hb : r ≫ b₀ = b := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointB c a b hcb.2.1
  have hx : r ≫ x₀ = x := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointX c a b x hbx.2.1 hax.2.1
  have hca' : r ≫ ca₀ = ca := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointCA c a b ca hca
  have hcb' : r ≫ cb₀ = cb := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointCB c a b cb hcb
  have hax' : r ≫ ax₀ = ax := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointAX c a b x ax hca.2.1 hbx.2.1 hax
  have hbx' : r ≫ bx₀ = bx := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointBX c a b x bx hcb.2.1 hax.2.1 hbx
  have hw : r ≫ w₀ = w := InterchangeParameterFactors.Construction.lineInterchangeParameterLift_pointW c a b cb ax w hcb hax.2.2 hby
  have hax₀ := InterchangeParameters.Construction.lineInterchangeRelationAX C B
  have hbx₀ := InterchangeParameters.Construction.lineInterchangeRelationBX C B
  have hcb₀ := InterchangeParameters.Construction.lineInterchangeRelationCB C B
  have hca₀ := InterchangeParameters.Construction.lineInterchangeRelationCA C B
  have hby₀ := InterchangeParameters.Construction.lineInterchangeRelationBY C B
  have haz₀ := InterchangeParameters.Construction.lineInterchangeRelationAZ C B
  have hg := GroupInterchange.Construction.picardImageGroupProducts_interchange D βv hβv βh hβh q i hfac c₀ a₀ b₀ x₀ ca₀ cb₀ ax₀ bx₀ w₀ hax₀ hbx₀ hcb₀ hca₀ hby₀ haz₀
  have hp := FiberInterchangePullback.Construction.fiberBilinear_interchange_pullback (L) r
    c₀ a₀ b₀ x₀ ca₀ cb₀ ax₀ bx₀ w₀ c a b x ca cb ax bx w hc ha hb hx hca' hcb' hax' hbx' hw
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a₀ x₀ ax₀ hax₀) (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac b₀ x₀ bx₀ hbx₀)
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac c₀ b₀ cb₀ hcb₀) (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac c₀ a₀ ca₀ hca₀)
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac cb₀ ax₀ w₀ hby₀) (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac ca₀ bx₀ w₀ haz₀) hg U sc sa sb sx
  rw [ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac r cb₀ ax₀ w₀ hby₀ cb ax w hby hcb' hax' hw,
    ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac r c₀ b₀ cb₀ hcb₀ c b cb hcb hc hb hcb',
    ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac r a₀ x₀ ax₀ hax₀ a x ax hax ha hx hax',
    ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac r ca₀ bx₀ w₀ haz₀ ca bx w haz hca' hbx' hw,
    ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac r c₀ a₀ ca₀ hca₀ c a ca hca hc ha hca',
    ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac r b₀ x₀ bx₀ hbx₀ b x bx hbx hb hx hbx'] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Interchange.Construction
