import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineCechFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechPresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittCohomologyFinite

/-! # Bounded Zero Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.BoundedZeroFiniteness

noncomputable section

/-! Finite generation of the original global zeroth-level crystalline Ext groups. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local instance coefficientLimits : HasLimitsOfSize.{u, u}
    (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}

local instance coefficientProducts : HasProducts.{u}
    (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  fun J => (coefficientLimits p k).has_limits_of_shape (Discrete J)

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (i : ℕ) :
    Module.Finite (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0 i) := by
  let I := CechCohomology.resolution p k X 0
  let : Module.Finite (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (((CechCoefficient.Total.bicomplex
        (FormalCoproduct.mk (EtaleCover.Index k X) (DeRhamZariski.opens k X)).cech
        (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I)).total (.up ℕ)).homology i) :=
    CrystallineCechFiniteness.total_finite p k X I hprojective i
  let : Module.Finite (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      ((CechCohomology.complex p k X 0).homology i) :=
    Module.Finite.equiv (HomologicalComplex.homologyMapIso
      (Bounded.CechPresheafCoordinates.totalIso (Witt.Crystalline.wittStructureMap p k X) 0 I
        (DeRhamZariski.opens k X)) i).symm.toLinearEquiv
  exact Module.Finite.equiv (CechCohomology.homologyIso p k X 0 i).toLinearEquiv

theorem finite_type (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (i : ℕ) :
    Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0 i) := by
  let : Module.Finite (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0 i) :=
    finite p k X hprojective i
  exact Bounded.WittCohomologyFinite.finite p k (Witt.Crystalline.wittStructureMap p k X) 0 i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.BoundedZeroFiniteness
