import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechConstants
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechObject
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import Mathlib.RingTheory.RingHom.Flat

/-! # Cech Flat -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechFlat.Construction

noncomputable section

/-! A finite affine Cech cover of a flat separated family has flat
native terms over the literal base ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u v

set_option backward.isDefEq.respectTransparency false in
theorem flat_restrictScalars_of_flat_hom {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (hρ : ρ.Flat) (M : ModuleCat.{v} S) [Module.Flat S M] :
    Module.Flat R ((ModuleCat.restrictScalars ρ).obj M) := by
  let : Algebra R S := ρ.toAlgebra
  let : Module R M := Module.compHom M ρ
  have : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  have : Module.Flat R S := hρ
  exact Module.Flat.trans R S M

set_option backward.isDefEq.respectTransparency false in
theorem relativeStructureCech_flat
    {R : Type u} [CommRing R] {X : Scheme.{u}} [X.IsSeparated]
    (f : X ⟶ Spec (.of R)) [Flat f]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Module.Flat R ((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X q) := by
  let M := (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U).X q
  have : Module.Flat Γ(Spec (.of R), ⊤) M :=
    Quotients.FiniteDescent.OrderedCechObject.Construction.OrderedCechFlat.complex f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
      (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)) U
      (fun d a => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU d a) q
  exact flat_restrictScalars_of_flat_hom (Scheme.ΓSpecIso (.of R)).inv.hom
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)) M

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechFlat.Construction
