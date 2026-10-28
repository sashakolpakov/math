import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourceBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantBlockIso

/-! # Polarized Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedBaseChange.Construction

noncomputable section

/-! The full polarized source-base-change theorem expressed through a
bundled abelian comparison and its native block isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of k)))
variable (B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of k')))
variable (f : Spec (.of k') ⟶ Spec (.of k))
variable (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (A.pullback f) B)

def polarizedBaseChangeBlockIso (n : ℕ) (τ : Gal(E/ℚ)) :
    (Over.pullback f).mapGrp.obj (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A.polarized A.action τ n) ≅
      CMPointsAt.Construction.l45ChosenBlock j iota hsplit B.polarized B.action τ n :=
  EquivariantBlockIso.Construction.equivariantBaseChangeBlockIso j iota hsplit A.polarized.abelian B.polarized.abelian
    A.action B.action f (PolarizedComponents.Construction.polarizedBaseChangeAbelianComparison A B f e) n τ

variable (n r : ℕ) (labels : (Fin r × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A.polarized A.action (labels (v, false)) n))
variable (J : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k'
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit B.polarized B.action (labels (v, false)) n))
variable (eH : ∀ v, (Over.pullback f).obj (H v).group.X ≅ (J v).group.X)
variable (heH : ∀ v, (eH v).hom ≫ (J v).inclusion.hom.hom =
  (Over.pullback f).map (H v).inclusion.hom.hom ≫
    (polarizedBaseChangeBlockIso j iota hsplit A B f e n (labels (v, false))).hom.hom.hom)

include heH in
theorem prescribedFullKernel_polarizedBaseChange (Q : Over (Spec (.of k')))
    (a : Q ⟶ (A.polarized.abelian.pullback f).scheme) :
    Prescription.Construction.prescribedFullKernel j iota hsplit B.polarized B.action n r labels J Q
      (a ≫ (PolarizedComponents.Construction.polarizedBaseChangeAbelianComparison A B f e).abelian.hom) ↔
    Prescription.Construction.prescribedFullKernel j iota hsplit A.polarized A.action n r labels H ((Over.map f).obj Q)
      (A.polarized.abelian.baseChangePointsMulEquiv f Q a) := by
  apply PrescribedSourceBaseChange.Construction.prescribedFullKernel_sourceBaseChange j iota hsplit A.polarized B.polarized
    A.action B.action f e.polarized e.action n r labels H J eH
  intro v
  exact heH v

theorem prescribedFullKernel_polarizedBaseChange_of_comparison
    (c : PolarizedComponents.Construction.EquivariantAbelianIso (A.polarized.abelian.pullback f) B.polarized.abelian
      (A.action.pullback f) B.action)
    (hc : c = PolarizedComponents.Construction.polarizedBaseChangeAbelianComparison A B f e)
    (heC : ∀ v, (eH v).hom ≫ (J v).inclusion.hom.hom =
      (Over.pullback f).map (H v).inclusion.hom.hom ≫
        (EquivariantBlockIso.Construction.equivariantBaseChangeBlockIso j iota hsplit A.polarized.abelian B.polarized.abelian
          A.action B.action f c n (labels (v, false))).hom.hom.hom)
    (Q : Over (Spec (.of k'))) (a : Q ⟶ (A.polarized.abelian.pullback f).scheme) :
    Prescription.Construction.prescribedFullKernel j iota hsplit B.polarized B.action n r labels J Q (a ≫ c.abelian.hom) ↔
    Prescription.Construction.prescribedFullKernel j iota hsplit A.polarized A.action n r labels H ((Over.map f).obj Q)
      (A.polarized.abelian.baseChangePointsMulEquiv f Q a) := by
  subst c
  exact prescribedFullKernel_polarizedBaseChange j iota hsplit A B f e n r labels H J eH heC Q a

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedBaseChange.Construction
