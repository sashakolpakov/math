import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.GeometricRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionGeometricDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers

/-! # Pure Torsion Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! Pure HilbertConstruction classification transfers the proved fiber rigidity from
its finite-type universal family to every test scheme. Etale detection
then proves independence of any independently prescribed full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [CharZero K] [Countable K]
    {g L N : ℕ} {δ : Fin g → ℕ}
    (M : Pure.Fine.PurePolarizedModel g δ L (Spec (.of K)))
    [LocallyOfFiniteType M.space.hom]

theorem Pure.Fine.PurePolarizedModel.geometric_abelian_eq_id (hM : M.IsFine) (hL : 3 ≤ L)
    (T : Over (Spec (.of K))) (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L T.left)
    {k : Type} [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ T.left)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback x) (A.pullback x)) :
    e.abelian.hom = 𝟙 (A.abelian.pullback x).scheme := by
  obtain ⟨f, ⟨a⟩, _⟩ := hM T A
  let c := (a.pullback x).symm.trans (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal f.left x)
  exact Pure.AutomorphismDescent.pure_abelian_eq_id_via e c
    (fun j => Pure.GeometricRigidity.pureGeometricPullback_abelian_eq_id M.space.hom M.universal hL (x ≫ f.left) j)

theorem Pure.Fine.PurePolarizedModel.auxiliary_automorphism_torsion_eq_id [NeZero N] (hM : M.IsFine) (hL : 3 ≤ L)
    (T : Over (Spec (.of K))) (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L T.left)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) :
    HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap N e.abelian.hom = 𝟙 (A.abelian.torsionScheme N) := by
  let : Etale (A.abelian.torsionScheme N).hom :=
    (TorsionEtaleAt.TorsionEtale.torsion_finite_etale A.abelian T.hom N).2
  apply (TorsionGeometricDetection.torsionMap_eq_of_geometric_pullbacks A.abelian A.abelian e.abelian.hom
    (𝟙 A.abelian.scheme) ?_).trans (HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap_id A.abelian N)
  intro k hk hclosed x
  exact (M.geometric_abelian_eq_id hM hL T A x (e.pullback x)).trans
    ((Over.pullback x).map_id A.abelian.scheme).symm

end

/-! An auxiliary-level isomorphism transports every independently
prescribed full level uniquely, on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover

theorem PureTorsionRigidity.preserves_level_of_torsionMap_eq_id {S : Scheme.{0}} {g N : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : A.scheme ⟶ A.scheme) [IsMonHom f]
    (hf : HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap N f = 𝟙 (A.torsionScheme N))
    (β : A.FullLevel N) : Level.Stabilizers.LevelCover.PreservesFullLevel β f := by
  intro T c
  let x := β.hom.app (.op T) c
  let q := (A.torsionSchemePointsEquiv N T).symm x
  have hx : q ≫ A.torsionInclusion N = x.val :=
    congrArg Subtype.val ((A.torsionSchemePointsEquiv N T).apply_symm_apply x)
  have h := congrArg (fun z => q ≫ z ≫ A.torsionInclusion N) hf
  rw [HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion, Category.id_comp,
    ← Category.assoc, hx] at h
  exact h

variable {K : Type} [Field K] [CharZero K] [Countable K]
    {g L N : ℕ} {δ : Fin g → ℕ}
    (M : Pure.Fine.PurePolarizedModel g δ L (Spec (.of K)))
    [LocallyOfFiniteType M.space.hom] [NeZero N]

theorem Pure.Fine.PurePolarizedModel.auxiliary_automorphism_preserves_level (hM : M.IsFine) (hL : 3 ≤ L)
    (T : Over (Spec (.of K))) (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L T.left)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) (β : A.abelian.FullLevel N) :
    Level.Stabilizers.LevelCover.PreservesFullLevel β e.abelian.hom :=
  PureTorsionRigidity.preserves_level_of_torsionMap_eq_id A.abelian e.abelian.hom
    (M.auxiliary_automorphism_torsion_eq_id hM hL T A e) β

theorem Pure.Fine.PurePolarizedModel.prescribed_level_transport_independent (hM : M.IsFine) (hL : 3 ≤ L)
    (T : Over (Spec (.of K))) (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L T.left)
    (a b : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) (β : A.abelian.FullLevel N) :
    β.transport a.abelian = β.transport b.abelian := by
  have h := M.auxiliary_automorphism_preserves_level hM hL T A (a.trans b.symm) β
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro U c
  have hc := h U c
  change (β.hom.app (.op U) c).val ≫ (a.abelian.hom ≫ b.abelian.inv) =
    (β.hom.app (.op U) c).val at hc
  have hh := congrArg (fun z => z ≫ b.abelian.hom) hc
  simpa only [HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport_basis, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using hh

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
