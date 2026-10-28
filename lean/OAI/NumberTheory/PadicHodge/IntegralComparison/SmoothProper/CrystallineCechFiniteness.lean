import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondReferenceFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientNoetherian

/-! # Crystalline Cech Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineCechFiniteness

noncomputable section

/-! Finite cohomology of the original zeroth-level crystalline presheaf Cech total. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex (OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X) 0 I
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechCover.bicomplex p k X L

def rowIso (i : ℕ) : IntegralComparison.Module.TotalSecondClasses.horizontal (K).flip i ≅
    CechHomology.Comparison.target p k X I i :=
  BicomplexHomology.iso K i ≪≫
    Crystalline.CechPresheafExactness.homologyIso (WittVector p k) (Crystalline.CechCover.nerve k X) L i

theorem row_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (i q : ℕ) :
    Module.Finite R ((IntegralComparison.Module.TotalSecondClasses.horizontal (K).flip i).homology q) := by
  let : Module.Finite R ((CechHomology.Comparison.target p k X I i).homology q) :=
    CechHomology.Comparison.finite p k X I i hprojective q
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (rowIso p k X I i) q).symm.toLinearEquiv

theorem total_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n : ℕ) :
    Module.Finite R (((K).total (.up ℕ)).homology n) := by
  let : IsNoetherianRing R := Witt.CoefficientNoetherian.coefficient p k
  exact IntegralComparison.Module.TotalSecondReferenceFiniteness.Reference.finite K n (fun q i _ => row_finite p k X I hprojective i q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineCechFiniteness
