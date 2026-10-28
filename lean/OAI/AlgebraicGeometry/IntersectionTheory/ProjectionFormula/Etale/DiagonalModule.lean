import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DiagonalSequence
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurjectiveQuotientBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceDimensionVanishing

/-! # Diagonal Module -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DiagonalModule

noncomputable section

/-! The base-changed native diagonal module is the quotient by the
coordinate regular sequence. Consequently its native Euler pairing
vanishes below the sequence's support-dimension threshold. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) K) A] [IsScalarTower K (MvPolynomial (Fin n) K) A]
  [Algebra.FormallyUnramified (MvPolynomial (Fin n) K) A]
  (L : Type u) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] [Algebra (DiagonalTensor.Ring K A) L]

attribute [local instance] DiagonalTensor.diagonalAlgebra

def quotientEquiv (hp : (KaehlerDifferential.ideal K A).map (algebraMap (DiagonalTensor.Ring K A) L) ≠ ⊤) :
    (ProjectionFormula.Flat.Extension.baseChange (DiagonalTensor.Ring K A) L).obj (DiagonalTensorNaturality.diagonal K A) ≃ₗ[L]
      Regular.SequenceModule.quotient L
        (DiagonalSequence.sequence K A n L (algebraMap (DiagonalTensor.Ring K A) L)) := by
  let e := SurjectiveQuotientBaseChange.equiv (DiagonalTensor.Ring K A) A L
    (fun a => ⟨DiagonalTensorNaturality.first K A a, (mul_one a : DiagonalTensor.multiplication K A (DiagonalTensorNaturality.first K A a) = a)⟩)
  have hi := DiagonalSequence.ideal K A n L (algebraMap (DiagonalTensor.Ring K A) L) hp
  exact e.trans (Submodule.quotEquivOfEq _ _ hi)

theorem euler_zero [Module.Flat (MvPolynomial (Fin n) K) A] [Module.Flat (DiagonalTensor.Ring K A) L]
    (hp : (KaehlerDifferential.ideal K A).map (algebraMap (DiagonalTensor.Ring K A) L) ≠ ⊤)
    (M : ModuleCat.{u} L) [Module.Finite L M]
    (hdim : ∀ p ∈ Module.support L M, ringKrullDim (L ⧸ p.asIdeal) < n)
    (hiso : Module.support L M ∩ Module.support L
      ((ProjectionFormula.Flat.Extension.baseChange (DiagonalTensor.Ring K A) L).obj (DiagonalTensorNaturality.diagonal K A)) ⊆ {IsLocalRing.closedPoint L}) :
    Tor.Euler.euler L M ((ProjectionFormula.Flat.Extension.baseChange (DiagonalTensor.Ring K A) L).obj (DiagonalTensorNaturality.diagonal K A)) n = 0 := by
  let rs := DiagonalSequence.sequence K A n L (algebraMap (DiagonalTensor.Ring K A) L)
  let e := quotientEquiv K A n L hp
  have hlen : rs.length = n := DiagonalSequence.length K A n L (algebraMap (DiagonalTensor.Ring K A) L)
  have hr := DiagonalSequence.regular K A n L (algebraMap (DiagonalTensor.Ring K A) L)
    (RingHom.flat_algebraMap_iff.mpr (inferInstanceAs (Module.Flat (DiagonalTensor.Ring K A) L))) hp
  have hi : Module.support L M ∩ Module.support L (Regular.SequenceModule.quotient L rs) ⊆
      {IsLocalRing.closedPoint L} := by rw [← e.support_eq]; exact hiso
  have hz := Regular.SequenceDimensionVanishing.euler_zero L rs hr M
    (by simpa only [hlen] using hdim) hi
  rw [Tor.EulerTransport.iso_right L M e.toModuleIso n]
  simpa only [hlen] using hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DiagonalModule
