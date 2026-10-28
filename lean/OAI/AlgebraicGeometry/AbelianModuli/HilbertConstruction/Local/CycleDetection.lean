import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologySectionLifting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomologyInjective

/-! # Cycle Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CycleDetection.LocalSectionLifting

noncomputable section

/-! A finite free detector of first fiber cohomology lifts all degree-zero
fiber cycles over a local ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (S : ShortComplex (ModuleCat.{u} R)) (N : ModuleCat.{u} R)

def detectorTarget : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (0 : ModuleCat.of R (Fin 0 → R) ⟶ N)
    (0 : N ⟶ ModuleCat.of R (Fin 0 → R)) (by simp)

def detectorMap (b : S.X₂ ⟶ N) (hb : S.f ≫ b = 0) : S ⟶ detectorTarget N where
  τ₁ := 0
  τ₂ := b
  τ₃ := 0
  comm₁₂ := (show (0 : S.X₁ ⟶ ModuleCat.of R (Fin 0 → R)) ≫
    (0 : ModuleCat.of R (Fin 0 → R) ⟶ N) = 0 from zero_comp).trans hb.symm
  comm₂₃ := (show b ≫ (0 : N ⟶ ModuleCat.of R (Fin 0 → R)) = 0 from comp_zero).trans
    (show S.g ≫ (0 : S.X₃ ⟶ ModuleCat.of R (Fin 0 → R)) = 0 from comp_zero).symm

theorem lift_cycle [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    [Module.Finite R N] [Module.Free R N]
    (b : S.X₂ ⟶ N) (hb : S.f ≫ b = 0)
    (hdetect : ∀ z : IsLocalRing.ResidueField R ⊗[R] S.X₂,
      S.g.hom.baseChange (IsLocalRing.ResidueField R) z = 0 →
      b.hom.baseChange (IsLocalRing.ResidueField R) z = 0 →
      z ∈ (S.f.hom.baseChange (IsLocalRing.ResidueField R)).range)
    (z : IsLocalRing.ResidueField R ⊗[R] S.X₁)
    (hz : S.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : S.X₁, S.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z := by
  let T := detectorTarget N
  have : Module.Finite R T.X₁ := inferInstanceAs (Module.Finite R (Fin 0 → R))
  have : Module.Free R T.X₁ := inferInstanceAs (Module.Free R (Fin 0 → R))
  have : Module.Finite R T.X₂ := inferInstanceAs (Module.Finite R N)
  have : Module.Free R T.X₂ := inferInstanceAs (Module.Free R N)
  have : Module.Finite R T.X₃ := inferInstanceAs (Module.Finite R (Fin 0 → R))
  have : Module.Free R T.X₃ := inferInstanceAs (Module.Free R (Fin 0 → R))
  apply HilbertConstruction.Finite.FreeSectionLifting.LocalSectionLifting.finiteFree_lift_residue_cycle_of_cohomology_injective S T
    (detectorMap S N b hb) rfl _ z hz
  apply HomologyInjective.HomologyInjectiveCriterion.injective
  intro w hw hbw
  apply hdetect w hw
  obtain ⟨v, hv⟩ := hbw
  exact hv.symm.trans (by
    change (0 : (Fin 0 → R) →ₗ[R] N).baseChange (IsLocalRing.ResidueField R) v = 0
    rw [LinearMap.baseChange_zero]
    rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CycleDetection.LocalSectionLifting
