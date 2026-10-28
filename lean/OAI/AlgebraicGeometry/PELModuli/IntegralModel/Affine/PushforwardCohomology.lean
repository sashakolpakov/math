import OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuasicoherentPushforward
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyExactFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Pushforward Cohomology -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PushforwardCohomology

noncomputable section

/-! Affine direct image preserves actual cohomology over the original
base ring. The comparison uses the actual inverse-image affine cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
open OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

universe u

def affinePushforwardCohomologyLinearEquiv
    {X Y B : Scheme.{u}} [Y.IsSeparated]
    (f : X ⟶ Y) [IsAffineHom f] (π : Y ⟶ B)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π ((pushforward f).obj M) n
    letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule (f ≫ π) M n
    SheafCohomology.AffineH.Projective.H ((pushforward f).obj M) n ≃ₗ[Γ(B, ⊤)] SheafCohomology.AffineH.Projective.H M n := by
  let W := (pushforward f).obj M
  have : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from f]; infer_instance⟩
  have : W.IsQuasicoherent := QuasicoherentPushforward.quasicoherent_pushforward_of_quasiCompact_separated f M
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π W n
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule (f ≫ π) M n
  let eY := SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv π W U hU hUa n
  let eP := HomologicalComplex.homologyMapIso
    (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f π M U) n
  let eX := SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv (f ≫ π) M
    (fun i => f ⁻¹ᵁ U i) (hU.comap f.base.hom) (fun i => (hUa i).preimage f) n
  exact eY.symm.trans (eP.symm.toLinearEquiv.trans eX)

theorem baseCohomologyFinite_affinePushforward_iff_of_cover
    {X Y B : Scheme.{u}} [Y.IsSeparated]
    (f : X ⟶ Y) [IsAffineHom f] (π : Y ⟶ B)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) :
    CohomologyExactFiniteness.BaseCohomologyFinite π ((pushforward f).obj M) ↔ CohomologyExactFiniteness.BaseCohomologyFinite (f ≫ π) M := by
  constructor <;> intro h n
  · let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π ((pushforward f).obj M) n
    let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule (f ≫ π) M n
    let := h n
    exact Module.Finite.equiv (affinePushforwardCohomologyLinearEquiv f π M U hU hUa n)
  · let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π ((pushforward f).obj M) n
    let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule (f ≫ π) M n
    let := h n
    exact Module.Finite.equiv (affinePushforwardCohomologyLinearEquiv f π M U hU hUa n).symm

theorem baseCohomologyFinite_affinePushforward_iff
    {X Y B : Scheme.{u}} [Y.IsSeparated]
    (f : X ⟶ Y) [IsAffineHom f] (π : Y ⟶ B)
    (M : X.Modules) [M.IsQuasicoherent] :
    CohomologyExactFiniteness.BaseCohomologyFinite π ((pushforward f).obj M) ↔ CohomologyExactFiniteness.BaseCohomologyFinite (f ≫ π) M := by
  let : LinearOrder Y.affineCover.I₀ := WellOrderingRel.isWellOrder.linearOrder
  exact baseCohomologyFinite_affinePushforward_iff_of_cover f π M
    (fun i => (Y.affineCover.f i).opensRange) Y.affineCover.isOpenCover_opensRange
    (fun i => isAffineOpen_opensRange (Y.affineCover.f i))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PushforwardCohomology
