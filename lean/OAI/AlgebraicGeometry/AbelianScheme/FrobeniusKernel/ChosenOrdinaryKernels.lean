import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionEmbedding

/-! # Chosen Ordinary Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction

noncomputable section

/-!
The chosen active kernels in native ordinary blocks: the multiplicative
line, each étale line, and the whole étale q-torsion plane. The last is
then embedded in q²-torsion with its original source group scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj IsMulCommutative

universe u

instance etaleGroupScheme_commutative (S : Scheme.{u}) (D : Type u) [CommGroup D] :
    IsCommMonObj (EtaleSubgroups.Construction.etaleGroupScheme S D).X := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  let φ : (T ⟶ (EtaleSubgroups.Construction.etaleGroupScheme S D).X) ≃* LocallyConstant T.left D :=
    ((EtaleSubgroups.Construction.etaleGroupPointIso S D).app (.op T)).groupIsoToMulEquiv
  apply φ.injective
  exact (φ.map_mul x y).trans ((mul_comm (φ x) (φ y)).trans (φ.map_mul y x).symm)

variable (K : Type u) [Field K] (q : ℕ) [Fact q.Prime]

/-- An actual ordinary active q-torsion splitting. -/
abbrev ActiveOrdinarySplitting (B : Grp (Over (Spec (.of K)))) :=
  B ≅ OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock K q 1 1 ⊗ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q

/-- The level-one ordinary splitting has exactly this active étale plane. -/
def activeOrdinarySplitting {B : Grp (Over (Spec (.of K)))}
    (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting K B q 1 1 2) : ActiveOrdinarySplitting K q B := by
  have h : OrdinaryBlocks.Construction.etaleOrdinaryBlock K q 1 2 = EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q := by
    exact congrArg (fun n => EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of K))
      (ULift.{u} (Multiplicative (Fin 2 → ZMod n)))) (pow_one q)
  exact e ≪≫ (Iso.refl (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock K q 1 1) ⊗ᵢ eqToIso h)

variable {B : Grp (Over (Spec (.of K)))} (e : ActiveOrdinarySplitting K q B)

def chosenActiveMultiplicative : OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock K q 1 1 ⟶ B :=
  AnnihilatorSheaf.Construction.splitFirstInclusion _ _ ≫ e.inv

def chosenActiveEtalePlane : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q ⟶ B :=
  AnnihilatorSheaf.Construction.splitSecondInclusion _ _ ≫ e.inv

def chosenActiveEtaleLine (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of K)) q L ⟶ B :=
  EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of K)) q L ≫ chosenActiveEtalePlane K q e

theorem chosenActiveEtalePlane_closed :
    IsClosedImmersion (chosenActiveEtalePlane K q e).hom.hom.left := by
  have : IsFinite (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock K q 1 1).X.hom :=
    (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock_finiteLocallyFree K q 1 1).1
  have : IsFinite (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q).X.hom :=
    EtaleSubgroups.Construction.etaleGroupScheme_finite _ _
  have := OrdinaryBlocks.Construction.splitSecondInclusion_closed (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock K q 1 1)
    (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q)
  have : IsIso e.inv.hom.hom.left := inferInstanceAs
    (IsIso (((Grp.forget (Over (Spec (.of K)))) ⋙ Over.forget _).map e.inv))
  change IsClosedImmersion
    ((AnnihilatorSheaf.Construction.splitSecondInclusion (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock K q 1 1)
      (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q)).hom.hom.left ≫ e.inv.hom.hom.left)
  infer_instance

theorem chosenActiveEtaleLine_closed (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    IsClosedImmersion (chosenActiveEtaleLine K q e L).hom.hom.left := by
  have := EtaleSubgroups.Construction.activeEtaleLineEmbedding_closed (Spec (.of K)) q L
  have := chosenActiveEtalePlane_closed K q e
  change IsClosedImmersion ((EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of K)) q L).hom.hom.left ≫
    (chosenActiveEtalePlane K q e).hom.hom.left)
  infer_instance

variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))

instance torsionLevelEmbedding_isMonHom {m n : ℕ} (hmn : m ∣ n) :
    IsMonHom (TorsionEmbedding.Construction.torsionLevelEmbedding A hmn) := by
  apply RepresentedGroups.Construction.isMonHom_of_point_operations
  · intro T
    apply (cancel_mono (A.torsionInclusion n)).mp
    rw [Category.assoc, TorsionEmbedding.Construction.torsionLevelEmbedding_inclusion, MonObj.one_comp, MonObj.one_comp]
  · intro T x y
    apply (cancel_mono (A.torsionInclusion n)).mp
    rw [Category.assoc, TorsionEmbedding.Construction.torsionLevelEmbedding_inclusion, MonObj.mul_comp,
      MonObj.mul_comp, Category.assoc, Category.assoc, TorsionEmbedding.Construction.torsionLevelEmbedding_inclusion]

/-- The q-torsion embedding is also a morphism for the native group laws. -/
def torsionLevelGroupEmbedding {m n : ℕ} (hmn : m ∣ n) : Assembly.Construction.torsionGroup A m ⟶ Assembly.Construction.torsionGroup A n :=
  Grp.homMk (TorsionEmbedding.Construction.torsionLevelEmbedding A hmn)

/-- The active plane used by Z retains the same source group as at level
one; only its inclusion is composed with A[q] → A[q²]. -/
def chosenPlaneAtLevelTwo
    (j : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q ⟶ Assembly.Construction.torsionGroup A q) :
    EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q ⟶ Assembly.Construction.torsionGroup A (q ^ 2) :=
  j ≫ torsionLevelGroupEmbedding K A (show q ∣ q ^ 2 from ⟨q, pow_two q⟩)

omit [Fact q.Prime] in
theorem chosenPlaneAtLevelTwo_inclusion
    (j : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q ⟶ Assembly.Construction.torsionGroup A q) :
    (chosenPlaneAtLevelTwo K q A j).hom.hom ≫ A.torsionInclusion (q ^ 2) =
      j.hom.hom ≫ A.torsionInclusion q :=
  TorsionEmbedding.Construction.qTorsionAtLevelTwo_inclusion A q j.hom.hom

omit [Fact q.Prime] in
theorem chosenPlaneAtLevelTwo_killedByQ
    (j : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q ⟶ Assembly.Construction.torsionGroup A q)
    (T : Over (Spec (.of K))) (x : T ⟶ (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of K)) q).X) :
    (x ≫ (chosenPlaneAtLevelTwo K q A j).hom.hom ≫ A.torsionInclusion (q ^ 2)) ^ q = 1 :=
  TorsionEmbedding.Construction.qTorsionAtLevelTwo_killedByQ A q j.hom.hom T x

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction
