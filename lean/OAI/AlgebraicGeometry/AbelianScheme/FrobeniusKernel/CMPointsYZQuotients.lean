import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTorsion

/-! # CM Points YZ Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction

noncomputable section

/-!
The full Y and Z kernels have the prescribed active subgroup, the compact
whole/identity prescription, and the actual opposite annihilator at each
level. Their abelian quotients and prime-to-q markings are constructed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def l45MultiplicativeHeights {s : ℕ} (compact : Fin s → Bool) : Fin (s + 1) → ℕ :=
  Fin.cases 1 (fun v => if compact v then 3 else 0)

def l45EtaleHeights {s : ℕ} (compact : Fin s → Bool) : Fin (s + 1) → ℕ :=
  Fin.cases 2 (fun v => if compact v then 0 else 3)

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (compact : Fin s → Bool)
variable (e : ∀ (n : ℕ) (v : Fin (s + 1)), OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n) q n
    (l45MultiplicativeHeights compact v) (l45EtaleHeights compact v))
variable (hdual : ∀ v : Fin (s + 1), PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

def l45OrdinaryCoordinatesFamily (n : ℕ) (v : Fin (s + 1)) :
    CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n) :=
  CMPointsAt.Construction.l45BlockCoordinates j iota hsplit PEL ρ (labels (v, false)) (e n v)

def l45YChosenFamily (L : EtaleSubgroups.Construction.ActiveEtaleLine q) : ∀ v : Fin (s + 1),
    FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) 1) :=
  Fin.cases (FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota hsplit PEL ρ (labels (0, false)) (e 1 0) L)
    (fun v => FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e 1 v.succ))

def l45ZChosenFamily : ∀ v : Fin (s + 1),
    FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) 2) :=
  Fin.cases (FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota hsplit PEL ρ (labels (0, false)) (e 1 0))
    (fun v => FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e 2 v.succ))

/-- At the active place the Z source is literally the q-torsion plane. -/
theorem l45ZChosenFamily_active_group :
    (l45ZChosenFamily j iota hsplit PEL ρ s labels compact e 0).group =
      EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q := rfl

theorem l45ZChosenFamily_active_inclusion :
    (l45ZChosenFamily j iota hsplit PEL ρ s labels compact e 0).inclusion.hom.hom ≫
      CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ 2 (labels (0, false)) =
        (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q (e 1 0))).hom.hom ≫
          CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ 1 (labels (0, false)) :=
  CMPointsAt.Construction.l45ActivePlaneAtLevelTwo_inclusion j iota hsplit PEL ρ (labels (0, false)) (e 1 0)

abbrev l45FullYKernel (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ 1 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 1)
    (l45YChosenFamily j iota hsplit PEL ρ s labels compact e L)

abbrev l45FullZKernel :=
  CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ 2 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 2)
    (l45ZChosenFamily j iota hsplit PEL ρ s labels compact e)

abbrev l45FullYKernelInclusion (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ 1 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 1)
    (l45YChosenFamily j iota hsplit PEL ρ s labels compact e L) hdual

abbrev l45FullZKernelInclusion :=
  CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ 2 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 2)
    (l45ZChosenFamily j iota hsplit PEL ρ s labels compact e) hdual

theorem l45FullYKernel_killed (L : EtaleSubgroups.Construction.ActiveEtaleLine q) (T : Over (Spec (.of k)))
    (a : T ⟶ (l45FullYKernel j iota hsplit PEL ρ s labels compact e L).X) :
    (a ≫ l45FullYKernelInclusion j iota hsplit PEL ρ s labels compact e hdual L) ^ q = 1 := by
  simpa only [pow_one] using CMPointsKernels.Construction.l45FullChosenKernel_killed j iota hsplit PEL ρ 1 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 1)
    (l45YChosenFamily j iota hsplit PEL ρ s labels compact e L) hdual T a

theorem l45FullZKernel_killed (T : Over (Spec (.of k)))
    (a : T ⟶ (l45FullZKernel j iota hsplit PEL ρ s labels compact e).X) :
    (a ≫ l45FullZKernelInclusion j iota hsplit PEL ρ s labels compact e hdual) ^ (q ^ 2) = 1 :=
  CMPointsKernels.Construction.l45FullChosenKernel_killed j iota hsplit PEL ρ 2 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 2)
    (l45ZChosenFamily j iota hsplit PEL ρ s labels compact e) hdual T a

variable [IsAlgClosed k]

abbrev l45FullYQuotient (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  CMPointsKernels.Construction.l45FullChosenKernelQuotient j iota hsplit PEL ρ 1 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 1)
    (l45YChosenFamily j iota hsplit PEL ρ s labels compact e L) hdual

abbrev l45FullZQuotient :=
  CMPointsKernels.Construction.l45FullChosenKernelQuotient j iota hsplit PEL ρ 2 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 2)
    (l45ZChosenFamily j iota hsplit PEL ρ s labels compact e) hdual

abbrev l45FullYQuotientLevel (hN : Nat.Coprime q N) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  CMPointsKernels.Construction.l45FullChosenQuotientLevel j iota hsplit PEL ρ 1 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 1)
    (l45YChosenFamily j iota hsplit PEL ρ s labels compact e L) hdual hN

abbrev l45FullZQuotientLevel (hN : Nat.Coprime q N) :=
  CMPointsKernels.Construction.l45FullChosenQuotientLevel j iota hsplit PEL ρ 2 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 2)
    (l45ZChosenFamily j iota hsplit PEL ρ s labels compact e) hdual hN

abbrev l45FullYQuotientAction (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  CMPointsAction.Construction.l45FullChosenQuotientAction j iota hsplit PEL ρ 1 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 1)
    (l45YChosenFamily j iota hsplit PEL ρ s labels compact e L) hdual

abbrev l45FullZQuotientAction :=
  CMPointsAction.Construction.l45FullChosenQuotientAction j iota hsplit PEL ρ 2 (s + 1) labels
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 2)
    (l45ZChosenFamily j iota hsplit PEL ρ s labels compact e) hdual

theorem l45FullYQuotient_qRank (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    Nat.card (PEL.abelian.torsionPoints q (Over.mk (𝟙 _))) =
      Nat.card ((l45FullYQuotient j iota hsplit PEL ρ s labels compact e hdual L).abelian.torsionPoints
        q (Over.mk (𝟙 _))) :=
  CMPointsTorsion.Construction.l45Isogeny_qRank_preserved j iota hsplit PEL ρ (s + 1) labels hdual
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 1)
    (l45FullYQuotient j iota hsplit PEL ρ s labels compact e hdual L).isogeny

theorem l45FullZQuotient_qRank :
    Nat.card (PEL.abelian.torsionPoints q (Over.mk (𝟙 _))) =
      Nat.card ((l45FullZQuotient j iota hsplit PEL ρ s labels compact e hdual).abelian.torsionPoints
        q (Over.mk (𝟙 _))) :=
  CMPointsTorsion.Construction.l45Isogeny_qRank_preserved j iota hsplit PEL ρ (s + 1) labels hdual
    (l45OrdinaryCoordinatesFamily j iota hsplit PEL ρ s labels compact e 1)
    (l45FullZQuotient j iota hsplit PEL ρ s labels compact e hdual).isogeny

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction
