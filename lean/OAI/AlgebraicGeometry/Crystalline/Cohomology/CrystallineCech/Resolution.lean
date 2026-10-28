import OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Resolution.CrystallineCechResolution

noncomputable section

/-!
# A Čech resolution on the native affine crystalline site

For a fixed smooth affine lift, the tuples of maps into its p-power
PD-envelope frames yield a canonical resolution of the native constant
coefficient sheaf. The objectwise contraction and exact sheafification
prove the augmentation is a quasi-isomorphism in every degree.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]
  (A : Type u) [CommRing A] [Algebra (WittVector p k) A]
  (r : A →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) A) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X

/-- Lift presentation sets to the coefficient universe used by the native site. -/
def presentations : (Site.Object p k X)ᵒᵖ ⥤ Type (u + 1) :=
  AffineFrameCover.CrystallineAffineFrameCover.presentations p k B A r hr hbase ⋙ uliftFunctor.{u + 1}

instance presentations_nonempty [Algebra.Smooth (WittVector p k) A]
    (T : (Site.Object p k X)ᵒᵖ) : Nonempty ((presentations p k B A r hr hbase).obj T) := by
  change Nonempty (ULift ((AffineFrameCover.CrystallineAffineFrameCover.presentations p k B A r hr hbase).obj T))
  infer_instance

/-- Free sheaves on tuples of actual maps into frame levels. -/
def complex : ChainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℕ :=
  Cech.PresentationResolution.CechPresentationResolution.sheafComplex R (presentations p k B A r hr hbase) J

/-- The canonical augmentation to Cohomology's native coefficient sheaf. -/
def augmentation : complex p k B A r hr hbase ⟶
    (ChainComplex.single₀ (Sheaf J (ModuleCat.{u + 1} R))).obj
      (Site.coefficientSheaf p k X) :=
  Cech.PresentationResolution.CechPresentationResolution.sheafAugmentation R (presentations p k B A r hr hbase) J

instance augmentation_quasiIso [Algebra.Smooth (WittVector p k) A] :
    QuasiIso (augmentation p k B A r hr hbase) :=
  Cech.PresentationResolution.CechPresentationResolution.sheafAugmentation_quasiIso R (presentations p k B A r hr hbase) J

def degreeZeroHomologyIso [Algebra.Smooth (WittVector p k) A] :
    (complex p k B A r hr hbase).homology 0 ≅ Site.coefficientSheaf p k X := by
  letI : QuasiIsoAt (augmentation p k B A r hr hbase) 0 :=
    (augmentation_quasiIso p k B A r hr hbase).quasiIsoAt 0
  exact isoOfQuasiIsoAt (augmentation p k B A r hr hbase) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
      (Site.coefficientSheaf p k X)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Resolution.CrystallineCechResolution
