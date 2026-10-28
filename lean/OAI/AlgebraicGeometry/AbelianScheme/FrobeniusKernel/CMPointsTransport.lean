import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockPointsTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveBlock
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Action
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusPoints

/-! # CM Points Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction

noncomputable section

/-!
Frobenius transport on the actual CMPoints source blocks. The map is induced
by the original abelian-scheme Frobenius and its proved action square.
Its etale-plane inverse is derived from geometric point bijectivity.
The q-torsion to q-squared-torsion embedding is retained exactly.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

/-- Name the original Frobenius pullback once so all block expressions
share the same native target data during elaboration. -/
def l45FrobeniusTargetAbelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)) :=
  A.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))

def l45FrobeniusTargetAction :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (l45FrobeniusTargetAbelian (q := q) k A) :=
  ρ.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))

def l45FrobeniusIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A (l45FrobeniusTargetAbelian (q := q) k A) :=
  Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A

omit [IsAlgClosed k] [NumberField E] [Algebra ℚ E] in
theorem l45FrobeniusTargetAction_intertwines (b : NumberField.RingOfIntegers E) :
    ρ.map b ≫ (l45FrobeniusIsogeny (q := q) k A).hom =
      (l45FrobeniusIsogeny (q := q) k A).hom ≫ (l45FrobeniusTargetAction (q := q) k A ρ).map b :=
  Action.Construction.relativeFrobenius_action_intertwines q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) ρ b

local notation "hchar" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)
local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ
local notation "F" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k A
local notation "hF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction_intertwines (q := q) k A ρ

def l45FrobeniusBlockMap (n : ℕ) (τ : Gal(E/ℚ)) :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit AF ρF n τ).toGrp :=
  PointsBlockPointsTransport.Construction.l45BlockMap j iota hsplit A AF ρ ρF (F).hom hF n τ

omit [IsAlgClosed k] in
theorem l45FrobeniusBlockMap_inclusion (n : ℕ) (τ : Gal(E/ℚ)) :
    (l45FrobeniusBlockMap j iota hsplit k A ρ n τ).hom.hom ≫
      CMPointsAt.Construction.l45BlockInclusion j iota hsplit AF ρF n τ =
    CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ ≫ (F).hom :=
  PointsBlockPointsTransport.Construction.l45BlockMap_inclusion j iota hsplit A AF ρ ρF (F).hom hF n τ

theorem l45FrobeniusBlockMap_points_bijective (n : ℕ) (τ : Gal(E/ℚ)) :
    Function.Bijective ((yonedaGrp.map (l45FrobeniusBlockMap j iota hsplit k A ρ n τ)).app
      (op (Over.mk (𝟙 _)))) :=
  PointsBlockPointsTransport.Construction.l45BlockMap_points_bijective j iota hsplit A AF ρ ρF (F).hom hF n τ (Over.mk (𝟙 _))
    (Picard.Homomorphisms.FrobeniusPoints.Construction.relativeFrobenius_points_bijective q (Fact.out : q.Prime) hchar A.scheme (𝟙 _))

omit [IsAlgClosed k] in
theorem l45FrobeniusBlockMap_level (τ : Gal(E/ℚ)) {n m : ℕ} (hnm : n ≤ m) :
    CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ hnm ≫
      l45FrobeniusBlockMap j iota hsplit k A ρ m τ =
    l45FrobeniusBlockMap j iota hsplit k A ρ n τ ≫
      CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit AF ρF τ hnm :=
  PointsBlockPointsTransport.Construction.l45BlockMap_level j iota hsplit A AF ρ ρF (F).hom hF τ hnm

variable (τ : Gal(E/ℚ))
variable (e : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)
variable (targetSplitting : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit
    (l45FrobeniusTargetAbelian (q := q) k A)
    (l45FrobeniusTargetAction (q := q) k A ρ) 1 τ).toGrp)

local notation "BG" => CommGrp.toGrp (OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ)
local notation "BFG" => CommGrp.toGrp (OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit AF ρF 1 τ)

/-- This record contains the original blocks and source map; its
point-bijectivity field is proved from the abelian Frobenius theorem. -/
def l45FrobeniusActiveTransportData : ActiveBlock.Construction.ActiveBlockTransportData k q where
  source := BG
  target := BFG
  sourceSplitting := e
  targetSplitting := targetSplitting
  map := l45FrobeniusBlockMap j iota hsplit k A ρ 1 τ
  pointsBijective := l45FrobeniusBlockMap_points_bijective j iota hsplit k A ρ 1 τ

/-- The plane map comes from the original Frobenius map of the native
CMPoints block, with no plane-bijection assumption. -/
def l45FrobeniusPlaneIso :
    EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ≅ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q :=
  (l45FrobeniusActiveTransportData j iota hsplit k A ρ τ e targetSplitting).planeIso

theorem l45FrobeniusPlaneIso_inclusion :
    (l45FrobeniusPlaneIso j iota hsplit k A ρ τ e targetSplitting).hom ≫ ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q targetSplitting =
      ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫ l45FrobeniusBlockMap j iota hsplit k A ρ 1 τ :=
  (l45FrobeniusActiveTransportData j iota hsplit k A ρ τ e targetSplitting).planeIso_inclusion

/-- Z transports the same q-plane with its level-two inclusion. -/
theorem l45FrobeniusPlaneIso_levelTwo :
    (l45FrobeniusPlaneIso j iota hsplit k A ρ τ e targetSplitting).hom ≫
      (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q targetSplitting ≫
        CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit AF ρF τ (show 1 ≤ 2 by decide)) =
    (ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e ≫
      CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ (show 1 ≤ 2 by decide)) ≫
        l45FrobeniusBlockMap j iota hsplit k A ρ 2 τ := by
  rw [← Category.assoc, l45FrobeniusPlaneIso_inclusion, Category.assoc,
    ← l45FrobeniusBlockMap_level, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction
