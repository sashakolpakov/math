import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex

/-! # Flasque Cech Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison

noncomputable section

/-! The original bounded crystalline injective resolution is computed by
the Cech total of its open-section complex for any small open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {ι : Type} (U : ι → Y.Opens)

def map := FlasqueCechGlobal.FlasqueCechGlobalComparison.map.{u + 1, u, u + 2} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier U
  (IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I)

theorem quasiIso (hU : iSup U = ⊤) : QuasiIso (map fY n I U) :=
  FlasqueCechGlobal.FlasqueCechGlobalComparison.quasiIso.{u + 1, u, u + 2} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier U
    (IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I) hU
      (IntegralComparison.BoundedOpen.FlasqueComplex.term_flasque fY n I)

def homologyIso (hU : iSup U = ⊤) (i : ℕ) :
    ((FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex.{u + 1, u, u + 2} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier U
      (IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I)).total (.up ℕ)).homology i ≅
    ModuleCat.of (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
      (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n i) := by
  let := quasiIso fY n I U hU
  exact (asIso (HomologicalComplex.homologyMap (map fY n I U) i)).symm ≪≫
    IntegralComparison.BoundedOpen.SectionGlobal.homologyIso fY n I i

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison
