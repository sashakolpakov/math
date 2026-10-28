import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.CohomologyDifference
import OAI.NumberTheory.PadicHodge.IntegralComparison.ShortExactHomologyKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedCohomologySequence

/-! # Finite Level Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteLevelKernel

noncomputable section

/-!
# IntegralComparison: a finite-level criterion for the kernel description of original crystalline cohomology

The hypothesis concerns the actual bounded crystalline Ext groups. No
geometric finiteness theorem is assumed or encoded in their definition.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.property (p := p) (J := J) (δ := δ) f
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.presheafComplex (p := p) (J := J) (δ := δ) f
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := p) (J := J) (δ := δ) f

theorem difference_epi (i : ℕ)
    [∀ n, Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)] :
    Epi (HomologicalComplex.homologyMap (S).g i) := by
  let (n : ℕ) : Finite ((CountableProductHomology.component R
      (BoundedSection.Family.complex R P (ModuleCat.of R R) A) n).homology i) :=
    Finite.of_injective _ (BoundedProductCohomology.componentLinearEquiv f n i).injective
  exact BoundedSection.CohomologyDifference.homology_difference_epi R P
    (BoundedSection.Reconstruction.monotone_property f) (ModuleCat.of R R) A i

theorem inclusion_mono_succ (i : ℕ)
    [∀ n, Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)] :
    Mono (HomologicalComplex.homologyMap (S).f (i + 1)) := by
  let := difference_epi (p := p) (J := J) (δ := δ) f i
  exact ShortExactHomologyKernel.mono_succ (S) (ResolutionComplexExact.shortExact f) i

theorem middle_mono (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)] :
    Mono (BoundedCohomologySequence.middle (p := p) (J := J) (δ := δ) f i).f := by
  let T := ResolutionHomologySequence.middle (p := p) (J := J) (δ := δ) f i
  let : Mono T.f := (inferInstance : Mono (HomologicalComplex.homologyMap (S).f i))
  let U := ModuleCat.uliftFunctor.{u + 2, u + 1} R
  let : Mono (T.map U).f := (inferInstance : Mono (U.map T.f))
  exact ShortComplexTransport.mono_f (T.map U)
    (BoundedCohomologySequence.sourceIso f i)
    (BoundedCohomologySequence.productIso f i)
    (BoundedCohomologySequence.productIso f i)

def kernelLinearEquiv (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)] :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i ≃ₗ[R]
      LinearMap.ker (BoundedCohomologySequence.middle (p := p) (J := J) (δ := δ) f i).g.hom := by
  letI := middle_mono (p := p) (J := J) (δ := δ) f i
  exact ShortExactHomologyKernel.kernelLinearEquiv
    (BoundedCohomologySequence.middle f i) (BoundedCohomologySequence.middle_exact f i)

def kernelLinearEquiv_succ (i : ℕ)
    [∀ n, Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)] :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f (i + 1) ≃ₗ[R]
      LinearMap.ker (BoundedCohomologySequence.middle (p := p) (J := J) (δ := δ) f (i + 1)).g.hom := by
  letI := inclusion_mono_succ (p := p) (J := J) (δ := δ) f i
  exact kernelLinearEquiv f (i + 1)

def kernelLinearEquiv_zero :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0 ≃ₗ[R]
      LinearMap.ker (BoundedCohomologySequence.middle (p := p) (J := J) (δ := δ) f 0).g.hom := by
  letI := ShortExactHomologyKernel.mono_zero (S) (ResolutionComplexExact.shortExact f)
  exact kernelLinearEquiv f 0

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteLevelKernel
