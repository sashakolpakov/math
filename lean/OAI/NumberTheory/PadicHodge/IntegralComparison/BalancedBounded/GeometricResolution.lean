import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolutionCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionExt

/-! # Geometric Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.GeometricResolution

noncomputable section

/-! Native geometric naturality of the balanced frame-to-Ext comparison.
The genuine map to the target injective resolution supplies the coefficient
comparison; no preservation of injective objects is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of (WittVector p k))}
  {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  [IsSeparated f] [IsSeparated fY]
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {ι κ : Type u} (FX : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (FY : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) (ρ : ι → κ)
  (α : ∀ i, (BoundedOpen.Equivalence.postcompose g hg n).obj (FX i) ⟶ FY (ρ i))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "t" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback.constantTransport (p := p) (J := J) (δ := δ) g hg n
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (p := p) (J := J) (δ := δ) g hg n
local notation "PX" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.complex (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology f n) R FX
local notation "PY" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.complex (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology fY n) R FY
local notation "εX" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.augmentation (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology f n) R FX
local notation "εY" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.augmentation (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology fY n) R FY
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup.resolution p k f n
local notation "IY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup.resolution p k fY n
local notation "β" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricRefinement.map T FX FY ρ α R (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology f n) (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology fY n)
local notation "γ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionMap.map g hg n IY IX

omit [CharP k p] [IsSeparated f] [IsSeparated fY] in
theorem extMap_eq (i : ℕ) :
    ResolutionHom.TransportCohomology.extMap S R (t).inv (s).hom i =
      ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ (t).inv)
    (x.mapExactFunctor S) (Abelian.Ext.mk₀ (s).hom) (zero_add i)).symm

omit [CharP k p] [IsSeparated f] [IsSeparated fY] in
theorem coefficientMap_eq : ResolutionHom.TransportEdges.coefficientMap S R PY PX β (s).hom =
    Bounded.GeometricResolutionCech.map p k g hg n FX FY ρ α := rfl

variable (hX : ∀ U, CoveringObjectsSheafDetection.sieve FX U ∈ BoundedCrystalline.Site.topology f n U)
  (hY : ∀ U, CoveringObjectsSheafDetection.sieve FY U ∈ BoundedCrystalline.Site.topology fY n U)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap
    (Bounded.GeometricResolutionCech.map p k g hg n FX FY ρ α) i ≫
      (CechCup.resolutionHomologyIso p k f n FX hX i).hom =
        (CechCup.resolutionHomologyIso p k fY n FY hY i).hom ≫
          ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  let : QuasiIso εX := CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u}
    (BoundedCrystalline.Site.topology f n) R FX hX
  let : QuasiIso εY := CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u}
    (BoundedCrystalline.Site.topology fY n) R FY hY
  have hn := Balanced.ResolutionCohomology.naturality R PY εY IY
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k fY n FY) S PX β εX IX
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k f n FX) γ (t).inv
    (Presentation.GeometricRefinement.augmentation_zero.{u + 1, u} T FX FY ρ α R
      (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)) (s).hom
    (BoundedGeneral.ResolutionExt.augmentation_square g hg n IY IX) i
  exact hn.trans (congrArg
    (fun a => (CechCup.resolutionHomologyIso p k fY n FY hY i).hom ≫ a)
    (extMap_eq p k (J := J) (δ := δ) g hg n i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.GeometricResolution
