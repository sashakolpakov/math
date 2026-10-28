import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Properties
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents

/-! # Embedded Active Families -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies

noncomputable section

/-! Embed an actual finite flat active kernel in the original abelian
source. Its relative model, torsion bound and projector support are
derived from the original inclusion, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

section

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Properties OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (n : ℕ) (p : A ⟶ A) [IsMonHom p] (K : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p))

def embeddedActiveMap : K.carrier ⟶ A := K.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p

instance embeddedActiveMap_isMonHom : IsMonHom (embeddedActiveMap n p K) :=
  inferInstanceAs (IsMonHom (K.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p))

instance embeddedActiveMap_mono : Mono (embeddedActiveMap n p K) := by
  have : IsClosedImmersion K.inclusion.left := K.closed
  have : Mono K.inclusion := Over.mono_of_mono_left K.inclusion
  exact inferInstanceAs (Mono (K.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p))

def embeddedActiveFamily : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P := Kernel.Base.fixedKernelFamily (embeddedActiveMap n p K)

def embeddedActiveFamilyModel : (embeddedActiveFamily (P := P) n p K).Model := by
  let : IsFinite K.carrier.hom := K.finite
  let : Flat K.carrier.hom := K.flat
  let : LocallyOfFinitePresentation K.carrier.hom := K.finitePresentation
  exact Kernel.Base.fixedKernelFamily_model (embeddedActiveMap n p K)

theorem embeddedActiveFamily_killed : (embeddedActiveFamily (P := P) n p K).KilledBy n := by
  rintro X t a ⟨b, rfl⟩
  change (b ≫ (K.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p)) ^ n = 1
  rw [← Category.assoc, ← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]

theorem embeddedActiveFamily_supported : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (embeddedActiveFamily (P := P) n p K) p := by
  rintro X t a ⟨b, rfl⟩
  change (b ≫ (K.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p)) ≫ p = _
  rw [Category.assoc, Category.assoc, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_supported]
  rfl

end

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Properties OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  {P : Over S} (τ : Gal(E/ℚ))
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ))))
  (n : ℕ) (hn : 1 ≤ n)

include hn in
theorem embeddedActiveFamily_killed_at_level :
    (embeddedActiveFamily (P := P) (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) H).KilledBy (q ^ n) :=
  Kernel.Models.killedBy_of_dvd _ (embeddedActiveFamily_killed _ _ H) (Nat.pow_dvd_pow q hn)

include hn in
theorem embeddedActiveFamily_supported_at_level :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (embeddedActiveFamily (P := P) (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) H)
      (ρ.map (j.projector iota hsplit n τ)) := by
  intro X t a ha
  have hk := embeddedActiveFamily_killed (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) H X t a ha
  have hs := embeddedActiveFamily_supported (q ^ 1) (ρ.map (j.projector iota hsplit 1 τ)) H X t a ha
  have he := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A ρ _ _ (q ^ 1)
    (by simpa only [Nat.cast_pow] using ProjectorLevels.projector_level_congruence j iota hsplit hn τ) X a hk
  exact he.trans hs

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies
