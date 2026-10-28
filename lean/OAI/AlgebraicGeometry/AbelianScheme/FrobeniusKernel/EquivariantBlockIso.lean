import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockSourceIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange

/-! # Equivariant Block Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantBlockIso.Construction

noncomputable section

/-! Native block transport and torsion-level compatibility for a bundled
equivariant abelian comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

local instance equivariantBlockMonoidal {X Y : Scheme} (f : X ⟶ Y) : (Over.pullback f).Monoidal :=
  Over.instBraidedPullback.toMonoidal

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
variable (c : PolarizedComponents.Construction.EquivariantAbelianIso A B ρ σ)

local instance equivariantAbelianBlockIso_group : IsMonHom c.abelian.hom := c.preservesGroup

def equivariantAbelianBlockIso (n : ℕ) (τ : Gal(E/ℚ)) :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ n τ).toGrp :=
  IntrinsicBlockSourceIso.Construction.l45NativeBlockSourceIso j iota hsplit A B ρ σ c.abelian c.action n τ

theorem equivariantAbelianBlockIso_level (τ : Gal(E/ℚ)) {n m : ℕ} (hnm : n ≤ m) :
    CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit A ρ τ hnm ≫
      (equivariantAbelianBlockIso j iota hsplit A B ρ σ c m τ).hom =
    (equivariantAbelianBlockIso j iota hsplit A B ρ σ c n τ).hom ≫
      CMPointsAt.Construction.l45BlockLevelEmbedding j iota hsplit B σ τ hnm :=
  PointsBlockPointsTransport.Construction.l45BlockMap_level j iota hsplit A B ρ σ c.abelian.hom c.action τ hnm

def equivariantBaseChangeBlockIso {S T : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g T)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B) (f : T ⟶ S)
    (c : PolarizedComponents.Construction.EquivariantAbelianIso (A.pullback f) B (ρ.pullback f) σ) (n : ℕ) (τ : Gal(E/ℚ)) :
    (Over.pullback f).mapGrp.obj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ n τ).toGrp :=
  IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ f n τ ≪≫
    equivariantAbelianBlockIso j iota hsplit (A.pullback f) B (ρ.pullback f) σ c n τ

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantBlockIso.Construction
