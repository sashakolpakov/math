import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELKernelTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers

/-! # Fiber Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Isogeny.FiberExtension.CM

noncomputable section

/-! Extend a full PEL isogeny between actual moduli fibers to a field
extension. The source and target comparisons are the canonical pullback
isomorphisms; the split kernel is the pullback of the original one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  {k L : Type} [Field k] [Field L] (σ : k →+* L)
  (b : Spec (.of k) ⟶ Spec (.of K))
  (x y : D.GeometricPoint b)

abbrev point (x : D.GeometricPoint b) := FieldPointDescent.CM.testMap σ b ≫ x

def familyIso (x : D.GeometricPoint b) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (D.fiberFamily (Spec.map (CommRingCat.ofHom σ) ≫ b) (point D σ b x))
      ((D.fiberFamily b x).pullback (Spec.map (CommRingCat.ofHom σ))) :=
  D.family.pullbackFactor (Spec.map (CommRingCat.ofHom σ)) x.left _ rfl

variable {n : ℕ} (e : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) n)

def isogeny :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily (Spec.map (CommRingCat.ofHom σ) ≫ b) (point D σ b x))
      (D.fiberFamily (Spec.map (CommRingCat.ofHom σ) ≫ b) (point D σ b y)) n :=
  (e.pullback (Spec.map (CommRingCat.ofHom σ))).transport
    (familyIso D σ b x) (familyIso D σ b y).symm

theorem splitKernel (χ : NumberField.RingOfIntegers E →+* ℤ_[q]) (m : ℕ) :
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (CM.isogeny D σ b x y e).isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (D.fiberFamily (Spec.map (CommRingCat.ofHom σ) ≫ b) (point D σ b x)) χ m) =
    (((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel e.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (D.fiberFamily b x) χ m)).pullback
      (Spec.map (CommRingCat.ofHom σ))).comapHom (familyIso D σ b x).abelian.hom := by
  rw [CM.isogeny, AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.splitKernel_transport, AbelianScheme.TateComparison.Subgroups.PointSubgroup.pullback_inf,
    AbelianScheme.TateComparison.Subgroups.PointSubgroup.pullback_kernel, AbelianScheme.TateComparison.SplitSubgroups.splitBlock_pullback]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Isogeny.FiberExtension.CM
