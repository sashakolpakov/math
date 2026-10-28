import OAI.RepresentationTheory.Theta.Geometric.PELComplementCompatibility
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction

/-! # Marked PEL Complement -/

namespace OAI.RepresentationTheory.Theta.Geometric.MarkedPELComplement

noncomputable section

/-! The original PEL isogeny has an actual complementary PEL isogeny,
with the full scalar marking shift, action, Poincare dual and polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
    {g N q m : ℕ} [Fact q.Prime]
    {P Q : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N (Spec (.of k))}
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q (q ^ m))
    (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
    (hQ : Q.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))
    (hqN : Nat.Coprime q N)

def markedPELComplement :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny Q (P.shiftMarking (ZMod.unitOfCoprime (q ^ m) (hqN.pow_left m))) (q ^ m) where
  isogeny := e.multiplierComplement δ hP hQ hq
  dualHom := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (e.multiplierComplement δ hP hQ hq).hom Q.dual P.dual
  dualGroup := PELComplementDual.nativeDualMap_group Q.dual P.dual (e.multiplierComplement δ hP hQ hq).hom
  poincare := (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualMap_poincare Q.dual P.dual (e.multiplierComplement δ hP hQ hq).hom).symm
  equivariant := PELComplementCompatibility.complementary_action e δ hP hQ hq
  polarization := PELComplementCompatibility.complementary_polarization e δ hP hQ hq
  marking T z := by
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData.shiftMarking_q_points]
    exact e.multiplierComplement_marking δ hP hQ hq T z

theorem markedPELComplement_comp :
    (markedPELComplement e δ hP hQ hq hqN).isogeny.hom ≫ e.isogeny.hom =
      (𝟙 Q.abelian.scheme) ^ (q ^ m) :=
  PELComplementCompatibility.complement_comp_isogeny e δ hP hQ hq

theorem comp_markedPELComplement :
    e.isogeny.hom ≫ (markedPELComplement e δ hP hQ hq hqN).isogeny.hom =
      (𝟙 P.abelian.scheme) ^ (q ^ m) :=
  PELComplementCompatibility.isogeny_comp_complement e δ hP hQ hq

end

end OAI.RepresentationTheory.Theta.Geometric.MarkedPELComplement
