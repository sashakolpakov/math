import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModelUnit
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Structure Cech Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.StructureCechModel

noncomputable section

/-! Construct a finite projective Cech model of the actual structure
sheaf of an abelian family, valid on every affine base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

structure AbelianStructureCechModel {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) where
  length : ℕ
  opens : Fin length → A.scheme.left.Opens
  covers : iSup opens = ⊤
  affine : ∀ i, IsAffineOpen (opens i)
  complex : CochainComplex (ModuleCat.{0} Γ(S, ⊤)) ℕ
  comparison : complex ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) opens
  quasi : QuasiIso comparison
  finite : ∀ q, Module.Finite Γ(S, ⊤) (complex.X q)
  projective : ∀ q, Module.Projective Γ(S, ⊤) (complex.X q)
  baseChange : ∀ (Y T : Scheme.{0}) [IsAffine T] (a : Y ⟶ A.scheme.left) (ρ : Y ⟶ T)
    (t : T ⟶ S) (hp : IsPullback a ρ A.scheme.hom t),
    QuasiIso (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a A.scheme.hom ρ t hp.w (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A.scheme.left) opens comparison)

theorem abelianStructureCechModel_nonempty
    {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) : Nonempty (AbelianStructureCechModel A) := by
  let : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  let L := HilbertConstruction.Line.Bundles.LineBundle.trivial A.scheme.left
  obtain ⟨n, U, ha, _, hcover⟩ := L.exists_finite_affine_frames
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr (hcover x)
  obtain ⟨D, φ, hφ, _, hf, hp, hbase⟩ :=
    PELModuli.IntegralModel.Proper.FlatCech.properFlat_exists_affine_baseChange_model A.scheme.hom L U hU ha
  exact ⟨{
    length := n
    opens := U
    covers := hU
    affine := ha
    complex := D
    comparison := φ
    quasi := hφ
    finite := hf
    projective := hp
    baseChange := hbase }⟩

namespace AbelianStructureCechModel

variable {S : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (F : AbelianStructureCechModel A)

def unitMap : Γ(S, ⊤) →ₗ[Γ(S, ⊤)] F.complex.X 0 := by
  let := F.quasi
  exact Cech.ModelUnit.CechModelUnit.unitMap A.scheme.hom F.opens F.covers F.comparison

theorem differential_unitMap : (F.complex.d 0 1).hom.comp F.unitMap = 0 := by
  let := F.quasi
  exact Cech.ModelUnit.CechModelUnit.differential_unitMap A.scheme.hom F.opens F.covers F.comparison

end AbelianStructureCechModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.StructureCechModel
