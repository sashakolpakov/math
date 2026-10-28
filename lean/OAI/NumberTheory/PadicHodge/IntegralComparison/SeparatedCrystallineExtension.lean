import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineSeparatedProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineEqualizer
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map
import OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredOrEmptyKan

/-! # Separated Crystalline Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SeparatedCrystallineExtension

noncomputable section

/-!
# IntegralComparison: exact crystalline extension over a separated scheme

Binary products and equalizers make every incoming factorization category
cofiltered or empty. Module colimits over their opposites are exact in
both cases. Thus extension is exact on the original sheaf categories,
and restriction preserves injectives without an affine hypothesis on X.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction (Coeff)

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]

abbrev Small := Crystalline.Site.AffineThickening p B J δ f
abbrev Big := BigCrystallineSite.Object p B J δ f
abbrev inclusion : Small (p := p) (J := J) (δ := δ) f ⥤ Big (p := p) (J := J) (δ := δ) f := BigCrystallineSite.fromSmall

instance hasBinaryProducts : HasBinaryProducts (Small (p := p) (J := J) (δ := δ) f) :=
  Small.CrystallineSeparatedProduct.hasBinaryProducts f (Fact.out : p.Prime).pos

instance hasEqualizers : HasEqualizers (Small (p := p) (J := J) (δ := δ) f) :=
  Small.CrystallineEqualizer.hasEqualizers (p := p) (B := B) (J := J) (δ := δ) (f := f)

instance inclusion_preservesBinaryProducts : PreservesLimitsOfShape (Discrete WalkingPair)
    (inclusion (p := p) (J := J) (δ := δ) f) :=
  Small.CrystallineSeparatedProduct.inclusion_preservesBinaryProducts f (Fact.out : p.Prime).pos

instance inclusion_preservesEqualizers : PreservesLimitsOfShape WalkingParallelPair
    (inclusion (p := p) (J := J) (δ := δ) f) where
  preservesLimit {K} := by
    have : PreservesLimit (parallelPair (K.map WalkingParallelPairHom.left) (K.map WalkingParallelPairHom.right))
        (inclusion (p := p) (J := J) (δ := δ) f) :=
      Small.CrystallineEqualizer.inclusion_preserves_equalizer _ _
    exact preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

abbrev SmallSheaf := Crystalline.Map.Comparison.SmallModuleSheaf (p := p) (J := J) (δ := δ) f
abbrev BigSheaf := Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f

abbrev restriction : BigSheaf (p := p) (J := J) (δ := δ) f ⥤ SmallSheaf (p := p) (J := J) (δ := δ) f :=
  Crystalline.Map.Comparison.restriction f

abbrev extension : SmallSheaf (p := p) (J := J) (δ := δ) f ⥤ BigSheaf (p := p) (J := J) (δ := δ) f :=
  (inclusion f).sheafPullback (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) Crystalline.Site.AffineThickening.topology BigCrystallineSite.Object.topology

def adjunction : extension (p := p) (J := J) (δ := δ) f ⊣ restriction f :=
  (inclusion f).sheafAdjunctionContinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) Crystalline.Site.AffineThickening.topology BigCrystallineSite.Object.topology

instance extension_leftAdjoint : (extension (p := p) (J := J) (δ := δ) f).IsLeftAdjoint := (adjunction f).isLeftAdjoint

instance extension_preservesFiniteLimits : PreservesFiniteLimits (extension (p := p) (J := J) (δ := δ) f) :=
  FilteredOrEmptyKan.sheafPullback_preservesFiniteLimits (Crystalline.ExactRestriction.Coeff (B := B))
    (inclusion f) Crystalline.Site.AffineThickening.topology BigCrystallineSite.Object.topology

instance extension_preservesFiniteColimits : PreservesFiniteColimits (extension (p := p) (J := J) (δ := δ) f) := by infer_instance

instance extension_additive : (extension (p := p) (J := J) (δ := δ) f).Additive :=
  Functor.additive_of_preserves_binary_products _

instance restriction_preservesInjectives : (restriction (p := p) (J := J) (δ := δ) f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SeparatedCrystallineExtension
