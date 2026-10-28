import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactOrdinaryPointType
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockSourceIso

/-! # CM Points Compact Type -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCompactType.Construction

noncomputable section

/-! The two compact ordinary types agree across the actual block
Frobenius and an equivariant identification of its target source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {g : ℕ}
variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
variable (eA : (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A).scheme ≅ B.scheme) [IsMonHom eA.hom]
variable (heA : ∀ z : NumberField.RingOfIntegers E,
  (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ).map z ≫ eA.hom = eA.hom ≫ σ.map z)
variable (τ : Gal(E/ℚ)) (b b' : Bool)
variable (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp q 1
  (if b then 3 else 0) (if b then 0 else 3))
variable (e' : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp q 1
  (if b' then 3 else 0) (if b' then 0 else 3))

include e e' heA in
theorem l45CompactType_frobenius_sourceIso : b = b' := by
  let F := CMPointsTransport.Construction.l45FrobeniusBlockMap j iota hsplit k A ρ 1 τ
  let c := IntrinsicBlockSourceIso.Construction.l45NativeBlockSourceIso j iota hsplit (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A) B
    (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ) σ eA heA 1 τ
  let T : Over (Spec (.of k)) := Over.mk (𝟙 _)
  have hF := CMPointsTransport.Construction.l45FrobeniusBlockMap_points_bijective j iota hsplit k A ρ 1 τ
  have hc := (((yonedaGrp.mapIso c).app (.op T)).groupIsoToMulEquiv).bijective
  have hm : (yonedaGrp.map (F ≫ c.hom)).app (.op T) =
      (yonedaGrp.map F).app (.op T) ≫ (yonedaGrp.map c.hom).app (.op T) :=
    NatTrans.congr_app (yonedaGrp.map_comp F c.hom) (.op T)
  have hcomp : Function.Bijective ((yonedaGrp.map (F ≫ c.hom)).app (.op T)) := by
    rw [hm]
    exact hc.comp hF
  exact CompactOrdinaryPointType.Construction.compactOrdinaryType_eq_of_points_bijective k q b b' e e' (F ≫ c.hom) hcomp

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCompactType.Construction
