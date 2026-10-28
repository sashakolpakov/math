import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Assembly

/-! # Paired Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
Assemble each chosen subgroup with its constructed Cartier annihilator
in the opposite block. The pairing is the ordinary-block duality input;
the opposite subgroup and its closed inclusion are constructed from it.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

section

variable {K : Type u} [Field K]
variable {G H B : Grp (Over (Spec (.of K)))}
variable (P : CartierModel.Construction.CartierCoordinates (.of K) G) (Q : CartierModel.Construction.CartierCoordinates (.of K) H)
variable (i : H ⟶ G) (pairing : B ≅ P.dualGroup)

/-- The actual opposite subgroup is transported by the specified Cartier
identification of the opposite block. -/
def CartierModel.Construction.CartierCoordinates.oppositeInclusion : P.annihilatorGroup Q i ⟶ B :=
  P.annihilatorInclusion Q i ≫ pairing.inv

theorem CartierModel.Construction.CartierCoordinates.oppositeInclusion_closed :
    IsClosedImmersion (P.oppositeInclusion Q i pairing).hom.hom.left := by
  have := P.annihilatorInclusion_closed Q i
  have : IsIso pairing.inv.hom.hom.left := inferInstanceAs
    (IsIso (((Grp.forget (Over (Spec (.of K)))) ⋙ Over.forget _).map pairing.inv))
  change IsClosedImmersion
    ((P.annihilatorInclusion Q i).hom.hom.left ≫ pairing.inv.hom.hom.left)
  infer_instance

def CartierModel.Construction.CartierCoordinates.pairedKernel : Grp (Over (Spec (.of K))) := H ⊗ P.annihilatorGroup Q i

def CartierModel.Construction.CartierCoordinates.pairedKernelInclusion : P.pairedKernel Q i ⟶ G ⊗ B :=
  i ⊗ₘ P.oppositeInclusion Q i pairing

theorem CartierModel.Construction.CartierCoordinates.pairedKernel_finiteLocallyFree [IsFinite H.X.hom] [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] :
    IsFinite (P.pairedKernel Q i).X.hom ∧ Flat (P.pairedKernel Q i).X.hom ∧
      LocallyOfFinitePresentation (P.pairedKernel Q i).X.hom := by
  have ha := P.annihilatorGroup_finiteLocallyFree_overField Q i
  have : Flat (P.annihilatorGroup Q i).X.hom := ha.2.1
  have : LocallyOfFinitePresentation (P.annihilatorGroup Q i).X.hom := ha.2.2
  change IsFinite (Limits.pullback.fst H.X.hom (P.annihilatorGroup Q i).X.hom ≫ H.X.hom) ∧
    Flat (Limits.pullback.fst H.X.hom (P.annihilatorGroup Q i).X.hom ≫ H.X.hom) ∧
    LocallyOfFinitePresentation
      (Limits.pullback.fst H.X.hom (P.annihilatorGroup Q i).X.hom ≫ H.X.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem CartierModel.Construction.CartierCoordinates.pairedKernelInclusion_closed (hi : IsClosedImmersion i.hom.hom.left) :
    IsClosedImmersion (P.pairedKernelInclusion Q i pairing).hom.hom.left := by
  let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{u}) :=
    ⟨fun f g hf hg => by
      let := hf
      let := hg
      exact IsClosedImmersion.comp f g⟩
  change IsClosedImmersion (i.hom.hom ⊗ₘ (P.oppositeInclusion Q i pairing).hom.hom).left
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u}) hi
    (P.oppositeInclusion_closed Q i pairing) i.hom.hom.w.symm
    (P.oppositeInclusion Q i pairing).hom.hom.w.symm

end

variable {K : Type u} [Field K] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
variable (n k : ℕ) (G H B : Fin k → Grp (Over (Spec (.of K))))
variable (P : ∀ v, CartierModel.Construction.CartierCoordinates (.of K) (G v))
variable (Q : ∀ v, CartierModel.Construction.CartierCoordinates (.of K) (H v))
variable (i : ∀ v, H v ⟶ G v) (pairing : ∀ v, B v ≅ (P v).dualGroup)
variable (split : Assembly.Construction.torsionGroup A n ≅ BlockProducts.Construction.groupBlockProduct k (fun v => G v ⊗ B v))

/-- The full subgroup uses the chosen kernels and their actual opposite
annihilators, then embeds their product through the n-torsion of A. -/
def PairedKernels.Construction.fullPairedKernelToAbelian :
    (BlockProducts.Construction.groupBlockProduct k (fun v => (P v).pairedKernel (Q v) (i v))).X ⟶ A.scheme :=
  Assembly.Construction.fullKernelToAbelian A n k (fun v => (P v).pairedKernel (Q v) (i v))
    (fun v => G v ⊗ B v) (fun v => (P v).pairedKernelInclusion (Q v) (i v) (pairing v)) split

instance PairedKernels.Construction.fullPairedKernelToAbelian_isMonHom :
    IsMonHom (PairedKernels.Construction.fullPairedKernelToAbelian A n k G H B P Q i pairing split) := by
  unfold PairedKernels.Construction.fullPairedKernelToAbelian
  infer_instance

theorem PairedKernels.Construction.fullPairedKernelToAbelian_closed (hi : ∀ v, IsClosedImmersion (i v).hom.hom.left) :
    IsClosedImmersion (PairedKernels.Construction.fullPairedKernelToAbelian A n k G H B P Q i pairing split).left :=
  Assembly.Construction.fullKernelToAbelian_closed A n k _ _ _
    (fun v => (P v).pairedKernelInclusion_closed (Q v) (i v) (pairing v) (hi v)) split

theorem PairedKernels.Construction.fullPairedKernel_finiteLocallyFree
    (hH : ∀ v, IsFinite (H v).X.hom ∧ Flat (H v).X.hom ∧
      LocallyOfFinitePresentation (H v).X.hom) :
    IsFinite (BlockProducts.Construction.groupBlockProduct k (fun v => (P v).pairedKernel (Q v) (i v))).X.hom ∧
      Flat (BlockProducts.Construction.groupBlockProduct k (fun v => (P v).pairedKernel (Q v) (i v))).X.hom ∧
      LocallyOfFinitePresentation
        (BlockProducts.Construction.groupBlockProduct k (fun v => (P v).pairedKernel (Q v) (i v))).X.hom :=
  BlockProducts.Construction.groupBlockProduct_finiteLocallyFree k _ (fun v => by
    have : IsFinite (H v).X.hom := (hH v).1
    have : Flat (H v).X.hom := (hH v).2.1
    have : LocallyOfFinitePresentation (H v).X.hom := (hH v).2.2
    exact (P v).pairedKernel_finiteLocallyFree (Q v) (i v))

theorem PairedKernels.Construction.fullPairedKernelToAbelian_killed (T : Over (Spec (.of K)))
    (x : T ⟶ (BlockProducts.Construction.groupBlockProduct k (fun v => (P v).pairedKernel (Q v) (i v))).X) :
    (x ≫ PairedKernels.Construction.fullPairedKernelToAbelian A n k G H B P Q i pairing split) ^ n = 1 :=
  Assembly.Construction.fullKernelToAbelian_killed A n k _ _ _ split T x

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
