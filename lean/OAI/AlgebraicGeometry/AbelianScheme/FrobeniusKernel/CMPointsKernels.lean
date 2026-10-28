import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplitting
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ConstructedQuotientData

/-! # CM Points Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction

noncomputable section

/-!
Full native chosen/opposite kernels and their geometric abelian quotients.
The global embedding uses the proved coefficient-projector decomposition;
the opposite subgroups use the specified source polarization duality.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

def l45FullChosenKernel : Grp (Over (Spec (.of k))) :=
  BlockProducts.Construction.groupBlockProduct s (fun v => (P v).pairedKernel (H v).coordinates (H v).inclusion)

def l45FullChosenKernelInclusion :
    (l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X ⟶ PEL.abelian.scheme :=
  PairedKernels.Construction.fullPairedKernelToAbelian PEL.abelian (q ^ n) s
    (fun v => CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n)
    (fun v => (H v).group)
    (fun v => CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, true)) n)
    P (fun v => (H v).coordinates) (fun v => (H v).inclusion)
    (fun v => CMPointsAt.Construction.l45PairingAtLevel j iota hsplit PEL ρ
      (labels (v, false)) (labels (v, true)) (hdual v) n (P v))
    (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit PEL.abelian ρ n s labels)

instance l45FullChosenKernelInclusion_isMonHom :
    IsMonHom (l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual) := by
  exact PairedKernels.Construction.fullPairedKernelToAbelian_isMonHom PEL.abelian (q ^ n) s _ _ _ P _ _ _ _

instance l45FullChosenKernelInclusion_closed :
    IsClosedImmersion (l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual).left :=
  PairedKernels.Construction.fullPairedKernelToAbelian_closed PEL.abelian (q ^ n) s _ _ _ P _ _ _ _
    (fun v => (H v).closed)

instance l45FullChosenKernelInclusion_mono :
    Mono (l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual) :=
  Over.mono_of_mono_left _

theorem l45FullChosenKernel_finiteLocallyFree :
    IsFinite (l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X.hom ∧
    Flat (l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X.hom ∧
    LocallyOfFinitePresentation (l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X.hom :=
  PairedKernels.Construction.fullPairedKernel_finiteLocallyFree s _ _ P _ _ (fun v => (H v).finiteLocallyFree)

theorem l45FullChosenKernel_killed (T : Over (Spec (.of k)))
    (a : T ⟶ (l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X) :
    (a ≫ l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual) ^ (q ^ n) = 1 :=
  PairedKernels.Construction.fullPairedKernelToAbelian_killed PEL.abelian (q ^ n) s _ _ _ P _ _ _ _ T a

variable [IsAlgClosed k]

/-- The target abelian scheme and quotient map are constructed. -/
def l45FullChosenKernelQuotient : GeometricQuotient.Construction.GeometricKernelQuotient PEL.abelian
    (l45FullChosenKernel j iota hsplit PEL ρ n s labels P H)
    (l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual) :=
  GeometricQuotient.Construction.geometricKernelQuotient PEL.abelian _ _
    (l45FullChosenKernelInclusion_closed j iota hsplit PEL ρ n s labels P H hdual)
    (l45FullChosenKernel_finiteLocallyFree j iota hsplit PEL ρ n s labels P H)

def l45FullChosenQuotientIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PEL.abelian
    (l45FullChosenKernelQuotient j iota hsplit PEL ρ n s labels P H hdual).abelian :=
  (l45FullChosenKernelQuotient j iota hsplit PEL ρ n s labels P H hdual).isogeny

def l45FullChosenQuotientLevel (hN : Nat.Coprime q N) :
    (l45FullChosenKernelQuotient j iota hsplit PEL ρ n s labels P H hdual).abelian.FullLevel N :=
  (l45FullChosenKernelQuotient j iota hsplit PEL ρ n s labels P H hdual).level
    (hN.pow_left n) (l45FullChosenKernel_killed j iota hsplit PEL ρ n s labels P H hdual) PEL.level

theorem l45FullChosenQuotientLevel_transports (hN : Nat.Coprime q N)
    (T : (Over (Spec (.of k)))ᵒᵖ)
    (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N (Spec (.of k))).obj T) :
    ((l45FullChosenQuotientLevel j iota hsplit PEL ρ n s labels P H hdual hN).hom.app T c).val =
      (PEL.level.hom.app T c).val ≫
        (l45FullChosenQuotientIsogeny j iota hsplit PEL ρ n s labels P H hdual).hom :=
  (l45FullChosenKernelQuotient j iota hsplit PEL ρ n s labels P H hdual).level_transports
    (hN.pow_left n) (l45FullChosenKernel_killed j iota hsplit PEL ρ n s labels P H hdual) PEL.level T c

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction
