import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison

/-! # Coefficient Pullback Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.CoefficientPullbackIso

noncomputable section

/-! A scheme isomorphism preserves line-bundle cohomology with any specified coefficient ring, in every degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def affinePushforwardCoefficientCohomologyIso
    {X Y : Scheme.{u}} [Y.IsSeparated] {R : Type u} [CommRing R]
    (f : X ⟶ Y) [IsAffineHom f] (c : R →+* Γ(Y, ⊤))
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.appTop.hom.comp c) q).obj M ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj ((Scheme.Modules.pushforward f).obj M) := by
  classical
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f M
  letI : LinearOrder Y.affineOpens := IsWellOrder.linearOrder (WellOrderingRel (α := Y.affineOpens))
  let U : Y.affineOpens → Y.Opens := fun V => V.1
  have hU : iSup U = ⊤ := iSup_affineOpens_eq_top Y
  have hA : ∀ V, IsAffineOpen (U V) := fun V => V.2
  exact (OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso (f.appTop.hom.comp c) M
      (fun V => f ⁻¹ᵁ U V) (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top f U hU)
      (fun V => (hA V).preimage f) q).symm ≪≫
    HomologicalComplex.homologyMapIso (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c M U) q ≪≫
    OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso c ((Scheme.Modules.pushforward f).obj M) U hU hA q

def lineBundleCoefficientCohomologyPullbackIso
    {X Y : Scheme.{u}} [Y.IsSeparated] {R : Type u} [CommRing R]
    (f : X ⟶ Y) [IsIso f] (c : R →+* Γ(Y, ⊤)) (L : Line.Bundles.LineBundle Y) (q : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.appTop.hom.comp c) q).obj
        (L.pullback f).sheaf ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj L.sheaf := by
  have : (L.pullback f).sheaf.IsQuasicoherent := (L.pullback f).isQuasicoherent
  have : (Scheme.Modules.pullback f).IsEquivalence := Affine.SectionAdjunction.AffineSectionAdjunction.pullback_equivalence (asIso f)
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf
  have : IsIso η := inferInstance
  exact affinePushforwardCoefficientCohomologyIso f c (L.pullback f).sheaf q ≪≫
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).mapIso (asIso η).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.CoefficientPullbackIso
