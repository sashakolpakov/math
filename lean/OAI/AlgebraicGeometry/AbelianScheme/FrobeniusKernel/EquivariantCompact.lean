import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCompactType
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedComponents

/-! # Equivariant Compact -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantCompact.Construction

noncomputable section

/-! Compact type preservation through a bundled equivariant comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {g : ℕ}
variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
variable (c : PolarizedComponents.Construction.EquivariantAbelianIso (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A) B
  (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) σ)
variable (τ : Gal(E/ℚ)) (b b' : Bool)
variable (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp q 1
  (if b then 3 else 0) (if b then 0 else 3))
variable (e' : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp q 1
  (if b' then 3 else 0) (if b' then 0 else 3))

include c e e' in
theorem compactType_frobenius_equivariant : b = b' := by
  have : IsMonHom c.abelian.hom := c.preservesGroup
  exact CMPointsCompactType.Construction.l45CompactType_frobenius_sourceIso j iota hsplit k A B ρ σ
    c.abelian c.action τ b b' e e'

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantCompact.Construction
