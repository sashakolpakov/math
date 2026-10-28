import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainMixedNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback

/-! # Geometric Resolution Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolutionCech

noncomputable section

/-! Geometric maps of covering frame resolutions compute exactly the
original bounded crystalline Ext pullback in every degree. -/

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
local notation "HY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fY n
local notation "HX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (p := p) (J := J) (δ := δ) g hg n

def rawMap := Acyclic.ChainFunctorNaturality.map S R HY (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology fY n) R FY) (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX)
  (Presentation.GeometricRefinement.map.{u + 1, u} T FX FY ρ α R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n))

def coefficientMap := Acyclic.ChainCoefficientNaturality.complexMap R (e).hom (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX)

def map : BoundedFrame.ResolutionCohomology.complex p k fY n FY ⟶
    BoundedFrame.ResolutionCohomology.complex p k f n FX :=
  rawMap p k g hg n FX FY ρ α ≫ coefficientMap p k g hg n FX

omit [IsSeparated fY] in
theorem restricted_acyclic (a q : ℕ) : Subsingleton
    (Abelian.Ext.{u + 2} (((CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX)).X a) ((S).obj HY) (q + 1)) := by
  let : Subsingleton (Abelian.Ext.{u + 2} (((CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX)).X a) HX (q + 1)) :=
    BoundedFrame.ResolutionAcyclicity.subsingleton p k f n FX a q
  exact (Etale.Frobenius.extIsoCongr R (Iso.refl (((CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX)).X a)) e (q + 1)).injective.subsingleton

variable (hX : ∀ U, CoveringObjectsSheafDetection.sieve FX U ∈ BoundedCrystalline.Site.topology f n U)
  (hY : ∀ U, CoveringObjectsSheafDetection.sieve FY U ∈ BoundedCrystalline.Site.topology fY n U)

def restrictedIso (i : ℕ) := by
  let η := CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX
  let : QuasiIso η := CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX hX
  exact Acyclic.ChainCohomology.homologyIso R ((S).obj HY)
    (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX) η
    (restricted_acyclic p k g hg n FX) i

def rawPullback (i : ℕ) :=
  IntegralComparison.Ext.SourceExactFunctorModule.component S R HY i
    (Opposite.op (BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) fY n)) ≫
      (IntegralComparison.Ext.ContravariantModuleFunctor.functor R ((S).obj HY) i).map
        (BoundedCrystalline.CrystallinePullback.constantTransport g hg n).inv.op

def postcompose (i : ℕ) := ModuleCat.ofHom ((Abelian.Ext.mk₀ (e).hom).postcompOfLinear R
  (BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n) (Nat.add_zero i))

omit [CharP k p] [IsSeparated f] [IsSeparated fY] in
theorem pullback_eq (i : ℕ) : rawPullback p k (J := J) (δ := δ) g hg n i ≫ postcompose p k (J := J) (δ := δ) g hg n i =
    ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

theorem raw_homology (i : ℕ) : HomologicalComplex.homologyMap (rawMap p k g hg n FX FY ρ α) i ≫
    (restrictedIso p k g hg n FX hX i).hom =
      (BoundedFrame.ResolutionCohomology.homologyIso p k fY n FY hY i).hom ≫ rawPullback p k (J := J) (δ := δ) g hg n i := by
  let ε := CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology fY n) R FY
  let η := CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX
  let : QuasiIso ε := CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u} (BoundedCrystalline.Site.topology fY n) R FY hY
  let : QuasiIso η := CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX hX
  exact Acyclic.ChainMixedNaturality.homology S R HY
    (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology fY n) R FY)
    (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX)
    (Presentation.GeometricRefinement.map.{u + 1, u} T FX FY ρ α R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)) ε η
    (BoundedCrystalline.CrystallinePullback.constantTransport g hg n).inv
    (Presentation.GeometricRefinement.augmentation_zero.{u + 1, u} T FX FY ρ α R
      (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n))
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k fY n FY)
    (restricted_acyclic p k g hg n FX) i

omit [IsSeparated fY] in
theorem coefficient_homology (i : ℕ) : HomologicalComplex.homologyMap (coefficientMap p k g hg n FX) i ≫
    (BoundedFrame.ResolutionCohomology.homologyIso p k f n FX hX i).hom =
      (restrictedIso p k g hg n FX hX i).hom ≫ postcompose p k (J := J) (δ := δ) g hg n i := by
  let η := CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX
  let : QuasiIso η := CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX hX
  exact Acyclic.ChainCoefficientNaturality.homology R (e).hom
    (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R FX) η
    (restricted_acyclic p k g hg n FX)
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k f n FX) i

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (GeometricResolutionCech.map p k g hg n FX FY ρ α) i ≫
    (BoundedFrame.ResolutionCohomology.homologyIso p k f n FX hX i).hom =
      (BoundedFrame.ResolutionCohomology.homologyIso p k fY n FY hY i).hom ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  let A := rawMap p k g hg n FX FY ρ α
  let B := coefficientMap p k g hg n FX
  let d := (BoundedFrame.ResolutionCohomology.homologyIso p k f n FX hX i).hom
  let cY := (BoundedFrame.ResolutionCohomology.homologyIso p k fY n FY hY i).hom
  let q := postcompose p k (J := J) (δ := δ) g hg n i
  exact (congrArg (fun a => a ≫ d) (HomologicalComplex.homologyMap_comp A B i)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => HomologicalComplex.homologyMap A i ≫ a)
        (coefficient_homology p k g hg n FX hX i)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ q) (raw_homology p k g hg n FX FY ρ α hX hY i)).trans
            ((Category.assoc _ _ _).trans (congrArg (fun a => cY ≫ a) (pullback_eq p k (J := J) (δ := δ) g hg n i)))))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolutionCech
